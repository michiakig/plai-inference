#lang plai

(abridged-test-output false)
(print-only-errors true)

(define (operator-symbol? x)
  (member x '(+ - *)))

(define (valid-identifier? id)
  (and (symbol? id)
       (not (member id '(true false + - * iszero bif with rec fun tempty tcons
                              tempty? tfirst trest)))))


(define-type Expr
  [num (n number?)]
  [id (v valid-identifier?)]
  [bool (b boolean?)]
  [bin-num-op (op operator-symbol?) (lhs Expr?) (rhs Expr?)]
  [iszero (e Expr?)]
  [bif (test Expr?) (then Expr?) (else Expr?)]
;  [with (bound-id valid-identifier?) (bound-body Expr?) (body Expr?)]
;  [rec (bound-id valid-identifier?) (bound-body Expr?) (body Expr?)]
  [fun (arg-id valid-identifier?) (body Expr?)]
  [app (fun-expr Expr?) (arg-expr Expr?)]
  [tempty]
  [tcons (first Expr?) (rest Expr?)]
  [tfirst (e Expr?)]
  [trest (e Expr?)]
  [istempty (e Expr?)])

(define-type Type
  [t-num]
  [t-bool]
  [t-list (elem Type?)]
  [t-fun (arg Type?) (result Type?)]
  [t-var (v symbol?)])


; parse :: S-exp -> Expr
(define (parse e)
  (cond
    [(and (symbol? e) (symbol=? e 'tempty)) (tempty)]
    [(number? e) (num e)]
    [(valid-identifier? e) (id e)]
    [(member e '(true false)) (bool (symbol=? e 'true))]
    [(list? e)
     (case (first e)
       [(+ - *) (bin-num-op (first e) (parse (second e)) (parse (third e)))]
       [(iszero) (iszero (parse (second e)))]
       [(bif) (bif (parse (second e)) (parse (third e)) (parse (fourth e)))]
;       [(with) (with (first (second e))
;                     (parse (second (second e)))
;                     (parse (third e)))]
       [(fun) (fun (first (second e)) (parse (third e)))]
       [(tcons) (tcons (parse (second e)) (parse (third e)))]
       [(tfirst) (tfirst (parse (second e)))]
       [(trest) (trest (parse (second e)))]
       [(istempty) (istempty (parse (second e)))]
       [else (app (parse (first e)) (parse (second e)))])]
    [else (error "not implemented yet")]))

;; type for Type, Expr, or type ctor applied to Tx
(define-type Tx
  [tx-type (t Type?)]
  [tx-expr (e Expr?)]
  [tx-fun (arg Tx?) (body Tx?)]
  [tx-list (elem Tx?)])

;; constraint type 
(define-type Constraint
  [=== (lhs Tx?) (rhs Tx?)])

; generate-constraints :: Expr -> Constraint set
(define (generate-constraints e)
  (type-case Expr e
    [id (v) (set)]
    [num (n) (set (=== (tx-expr e) (tx-type (t-num))))]
    [bool (b) (set (=== (tx-expr e) (tx-type (t-bool))))]
    [iszero (arg) (set (=== (tx-expr e) (tx-type (t-bool)))
                       (=== (tx-expr arg) (tx-type (t-num))))]
    [bin-num-op (op x y)
                (set-union
                 (generate-constraints x)
                 (generate-constraints y)
                 (set
                  (=== (tx-expr x) (tx-type (t-num)))
                  (=== (tx-expr y) (tx-type (t-num)))
                  (=== (tx-expr e) (tx-type (t-num)))))]
    [bif (test then else)
         (set-union
          (set
           (=== (tx-expr e) (tx-expr then))
           (=== (tx-expr e) (tx-expr else)))
          (generate-constraints test)
          (generate-constraints then)
          (generate-constraints else))]
    [tempty () (set (=== (tx-expr e) (tx-type (t-list (t-var (gensym))))))]
    [istempty (arg)
              (set (=== (tx-expr e) (tx-type (t-bool)))
                   (=== (tx-expr arg) (tx-type (t-list (t-var (gensym))))))]
    [tfirst (arg) (set (=== (tx-expr e) (tx-type (t-var (gensym))))
                       (=== (tx-expr arg) (tx-list (tx-expr e))))]
    [trest (arg) (set (=== (tx-expr e) (tx-type (t-list (t-var (gensym)))))
                      (=== (tx-expr arg) (tx-type (t-list (t-var (gensym)))))
                      ;??? (=== (tx-expr arg) (tx-expr e))
                      )]
    [tcons (arg1 arg2) (set-union
                        (generate-constraints arg1)
                        (generate-constraints arg2)
                        (set
                         (=== (tx-expr e) (tx-list (tx-expr arg1)))
                         (=== (tx-expr arg2) (tx-list (tx-expr arg1)))))]
    [fun (arg body)
         (set-add
          (generate-constraints body)
          (=== (tx-expr e) (tx-fun (tx-expr (id arg)) (tx-expr body))))]
;    [with (bound-id bound-body body)
;          (set-union
;           (set (=== (tx-expr e) (tx-expr body))
;                (=== (tx-expr (id bound-id)) (tx-expr bound-body)))
;           (generate-constraints bound-body)
;           (generate-constraints body))]
    [app (fun arg)
         (set-add (set-union
                   (generate-constraints fun)
                   (generate-constraints arg))
                  (=== (tx-expr fun)
                       (tx-fun (tx-expr arg) (tx-expr e))))]))

(define-type Substitution
  [--> (x Expr?) (y Tx?)])

;; Tx Substitution -> Tx
(define (tx-replace tx subst)
  (let [(x (-->-x subst))
        (y (-->-y subst))]
    (match tx
      [(tx-fun arg body) (tx-fun (tx-replace arg subst)
                                 (tx-replace body subst))]
      [(tx-list arg) (tx-list (tx-replace arg subst))]
      [(tx-expr e) (if (equal? x e) y tx)]
      [(tx-type t) tx])))

;; "step 2" in PLAI p.280
;; replace :: Substitution Constraint/Substitution -> Constraint/Substitution
(define ((replace subst) cs)
  (match cs
    [(=== lhs rhs) (=== (tx-replace lhs subst) (tx-replace rhs subst))]
    [(--> lhs rhs) (--> lhs (tx-replace rhs subst))]))

(define (-set-map f s)
  (apply set (set-map s f)))

;; unify :: set of Constraints -> set of Substitutions
(define (unify constraints)
  (define (recur stack acc)
    (if (empty? stack)
        acc
        (let [(c (first stack))
              (cs (rest stack))]
;          (display "stack:")
;          (pretty-print stack)
;          (display "acc:")
;          (pretty-print acc)
;          (newline)
          (match c
            [(=== (tx-expr x) rhs)
             (let* [(subst (--> x rhs))
                    (r (replace subst))]
               (recur (map r cs) (set-add (-set-map r acc) subst)))]
            [(=== lhs (tx-expr y))
             (let* [(subst (--> y lhs))
                    (r (replace subst))]
               (recur (map (replace subst) cs) (set-add (-set-map r acc) subst)))]
            [(=== (tx-fun arg1 body1) (tx-fun arg2 body2))
             (recur (append (list (=== body1 body2)
                                  (=== arg1 arg2))
                            cs)
               acc)]
            [(=== (tx-list arg1) (tx-list arg2))
             (recur (cons (=== arg1 arg2) cs)
               acc)]
            [(=== (tx-type (t-list arg1)) (tx-list arg2))
             (recur (cons (=== (tx-type arg1) arg2) cs)
               acc)]
            [(=== (tx-list arg1) (tx-type (t-list arg2))) 
             (recur (cons (=== arg1 (tx-type arg2)) cs)
               acc)]
            [(=== lhs rhs)
             (if ((tx=? lhs) rhs)
                 (recur cs acc)
                 (error (format "unify error: in constraint ~v" c)))]))))
  (recur (set->list constraints) (set)))

; infer-type :: Expr -> Type
#;(define infer-type
  ...)


; type=? Type -> Type -> Bool
; signals an error if arguments are not variants of Type
; If you use this function in your test suite, include it with your test suite
; for war-grading.  So, you are free to modify this function as you see fit.
(define ((type=? t1) t2)
  (local ([define ht1 (make-hash)] ; maps vars in t1 to vars in t2
          [define ht2 (make-hash)] ; vice versa
          [define (teq? t1 t2)
            (cond
              [(and (t-num? t1) (t-num? t2)) true]
              [(and (t-bool? t1) (t-bool? t2)) true]
              [(and (t-list? t1) (t-list? t2))
               (teq? (t-list-elem t1) (t-list-elem t2))]
              [(and (t-fun? t1) (t-fun? t2))
               (and (teq? (t-fun-arg t1) (t-fun-arg t2))
                    (teq? (t-fun-result t1) (t-fun-result t2)))]
              [(and (t-var? t1) (t-var? t2))
               (local ([define v1 ; the symbol that ht1 says that t1 maps to
                         (hash-ref 
                          ht1 (t-var-v t1)
                          (lambda ()
                            ; if t1 doesn't map to anything, it's the first time
                            ; we're seeing it, so map it to t2
                            (hash-set! ht1 (t-var-v t1) (t-var-v t2))
                            (t-var-v t2)))]
                       [define v2
                         (hash-ref
                          ht2 (t-var-v t2)
                          (lambda ()
                            (hash-set! ht2 (t-var-v t2) (t-var-v t1))
                            (t-var-v t1)))])
                 ; we have to check both mappings, so that distinct variables
                 ; are kept distinct. i.e. a -> b should not be isomorphic to
                 ; c -> c under the one-way mapping a => c, b => c.
                 (and (symbol=? (t-var-v t2) v1) (symbol=? (t-var-v t1) v2)))]
              [(and (Type? t1) (Type? t2)) false]
              [else (error 'type=? "either ~a or ~a is not a Type" t1 t2)])])
    (teq? t1 t2)))

(test/pred (t-var 'a) 
           (type=? (t-var 'b)))
(test/pred (t-fun (t-var 'a) (t-var 'b)) 
           (type=? (t-fun (t-var (gensym)) (t-var (gensym)))))
(test/pred (t-fun (t-var 'a) (t-var 'b)) 
           (type=? (t-fun (t-var (gensym)) (t-var (gensym)))))
;(test/pred (t-fun (t-var 'a) (t-var 'a)) ; fails
;           (type=? (t-fun (t-var (gensym)) (t-var (gensym)))))
;(test/pred (t-fun (t-var 'a) (t-var 'b)) ;fails
;           (type=? (t-fun (t-var 'c) (t-var 'c))))
(test/exn ((type=? 34) 34) "not a Type")

;; Parsing tests

(test (parse '{a b}) (app (id 'a) (id 'b)))

(test (parse 'tempty) (tempty))

(test (parse '{tcons 1 tempty}) (tcons (num 1) (tempty)))
(test (parse '{tfirst {tcons 1 tempty}}) (tfirst (tcons (num 1) (tempty))))
(test (parse '{trest {tcons 1 tempty}}) (trest (tcons (num 1) (tempty))))
(test (parse '{istempty {tcons 1 tempty}}) (istempty (tcons (num 1) (tempty))))
(test (parse '{istempty tempty}) (istempty (tempty)))

(test (parse 1) (num 1))
(test (parse 12345) (num 12345))
(test (parse 1.2345) (num 1.2345))

(test (parse 'a) (id 'a))
(test (parse 'foo) (id 'foo))

(test (parse 'true) (bool true))
(test (parse 'false) (bool false))

(test (parse '{* 2 3}) (bin-num-op '* (num 2) (num 3)))
(test (parse '{+ 1 2}) (bin-num-op '+ (num 1) (num 2)))
(test (parse '{- 3 4}) (bin-num-op '- (num 3) (num 4)))
(test (parse '{* a b}) (bin-num-op '* (id 'a) (id 'b)))

(test (parse '{iszero 0}) (iszero (num 0)))

(test (parse '{bif true 1 2}) (bif (bool true) (num 1) (num 2)))
(test (parse '{bif a b c}) (bif (id 'a) (id 'b) (id 'c)))

;(test (parse '{with {a 1} {+ a b}})
;      (with 'a (num 1) (bin-num-op '+ (id 'a) (id 'b))))

(test (parse '{fun {x} {+ x x}})
      (fun 'x (bin-num-op '+ (id 'x) (id 'x))))

(test (parse '{a b}) (app (id 'a) (id 'b)))
(test (parse '{{fun {x} {* x x}} 2})
     (app (fun 'x (bin-num-op '* (id 'x) (id 'x))) (num 2)))

;; Tx -> Tx -> bool
;; compares two Txes for equality, using type=?
(define ((tx=? t1) t2)
  (if (and (tx-type? t1) (tx-type? t2))
      ((type=? (tx-type-t t1)) (tx-type-t t2))
      (equal? t1 t2)))

(test/pred (tx-type (t-num)) (tx=? (tx-type (t-num))))
(test/pred (tx-type (t-var 'a)) (tx=? (tx-type (t-var 'b))))
(test/pred (tx-expr (id 'a)) (tx=? (tx-expr (id 'a))))
(test/pred (tx-fun (tx-expr (id 'a)) (tx-expr (id 'b)))
           (tx=? (tx-fun (tx-expr (id 'a)) (tx-expr (id 'b)))))
(test/pred (tx-list (tx-expr (id 'a))) (tx=? (tx-list (tx-expr (id 'a)))))
(test false ((tx=? (tx-type (t-var 'g107244)))
             (tx-type (t-num))))

;; Constraint generation tests

;; Constraint -> Constraint -> bool
;; compares two constraints for equality, using tx=?
(define ((constraint=? c1) c2)
  (let [(lhs1 (===-lhs c1))
        (lhs2 (===-lhs c2))
        (rhs1 (===-rhs c1))
        (rhs2 (===-rhs c2))]
    (or (and ((tx=? lhs1) lhs2)
             ((tx=? rhs1) rhs2))
        (and ((tx=? lhs1) rhs2)
             ((tx=? rhs1) lhs2)))))

(test/pred (=== (tx-expr (id 'a)) (tx-type (t-var (gensym 'a))))
           (constraint=? (=== (tx-expr (id 'a)) (tx-type (t-var (gensym 'a))))))
(test/pred (=== (tx-expr (id 'a)) (tx-expr (id 'b)))
           (constraint=? (=== (tx-expr (id 'a)) (tx-expr (id 'b)))))
(test/pred (=== (tx-expr (id 'b)) (tx-expr (id 'a)))
           (constraint=? (=== (tx-expr (id 'a)) (tx-expr (id 'b)))))
(test/pred (=== (tx-expr (id 'a)) (tx-list (tx-expr (id 'b))))
           (constraint=? (=== (tx-list (tx-expr (id 'b))) (tx-expr (id 'a)))))

;; set of Constraint -> set of Constraint -> bool
;; compares two sets of constraints for equality, using constraint=?
(define ((constraint-set=? s1) s2)
  (local
    [(define list1 (set->list s1))
     (define list2 (set->list s2))]
    (and (equal? (set-count s1) (set-count s2))
         (foldl (lambda (x acc) (and acc (findf (constraint=? x) list1)))
                #t
                list2)
         (foldl (lambda (x acc) (and acc (findf (constraint=? x) list2)))
                #t
                list1))))

(test/pred (set) (constraint-set=? (set)))
(test/pred (set (=== (tx-expr (id 'a)) (tx-type (t-var (gensym 'a)))))
           (constraint-set=?
            (set (=== (tx-expr (id 'a)) (tx-type (t-var (gensym 'a)))))))
(test/pred (set
            (=== (tx-expr (id 'a)) (tx-type (t-var (gensym 'a))))
            (=== (tx-expr (id 'a)) (tx-expr (id 'b))))
           (constraint-set=?
            (set
             (=== (tx-expr (id 'a)) (tx-type (t-var (gensym 'b))))
             (=== (tx-expr (id 'a)) (tx-expr (id 'b))))))

;; abstraction
(test/pred (generate-constraints (fun 'y (bin-num-op '+ (id 'y) (id 'y))))
           (constraint-set=?
            (set (=== (tx-expr (fun 'y (bin-num-op '+ (id 'y) (id 'y))))
                      (tx-fun (tx-expr (id 'y))
                              (tx-expr (bin-num-op '+ (id 'y) (id 'y)))))
                 (=== (tx-expr (bin-num-op '+ (id 'y) (id 'y)))
                      (tx-type (t-num)))
                 (=== (tx-expr (id 'y)) (tx-type (t-num))))))

;; application
(test/pred (generate-constraints (app (id 'f) (id 'x)))
           (constraint-set=?
            (set (=== (tx-expr (id 'f))
                      (tx-fun (tx-expr (id 'x)) (tx-expr (app (id 'f) (id 'x))))))))
(let [(expr (app (fun 'x (bin-num-op '+ (id 'x) (id 'x))) (num 2)))]
  (test/pred (generate-constraints expr)
             (constraint-set=?
              (set-union
               (set (=== (tx-expr (app-fun-expr expr))
                         (tx-fun (tx-expr (app-arg-expr expr)) (tx-expr expr))))
               (generate-constraints (app-arg-expr expr))
               (generate-constraints (app-fun-expr expr))))))

;; with
;(test/pred (generate-constraints (with 'x (num 1) (bin-num-op '+ (id 'x) (id 'x))))
;           (constraint-set=?
;            (set-union
;             (set (=== (tx-expr (id 'x)) (tx-expr (num 1)))
;                  (=== (tx-expr (with 'x (num 1) (bin-num-op '+ (id 'x) (id 'x))))
;                       (tx-expr (bin-num-op '+ (id 'x) (id 'x)))))
;             (generate-constraints (num 1))
;             (generate-constraints (bin-num-op '+ (id 'x) (id 'x))))))

;; literals
(test/pred (generate-constraints (num 1))
           (constraint-set=? (set (=== (tx-expr (num 1)) (tx-type (t-num))))))
(test/pred (generate-constraints (bool true))
           (constraint-set=? (set (=== (tx-expr (bool true)) (tx-type (t-bool))))))
(test/pred (generate-constraints (bool false))
           (constraint-set=? (set (=== (tx-expr (bool false)) (tx-type (t-bool))))))

;; binary number ops
(test/pred (generate-constraints (bin-num-op '+ (num 1) (num 2)))
      (constraint-set=?
       (set (=== (tx-expr (bin-num-op '+ (num 1) (num 2))) (tx-type (t-num)))
            (=== (tx-expr (num 1)) (tx-type (t-num)))
            (=== (tx-expr (num 2)) (tx-type (t-num))))))

;; if
(test/pred (generate-constraints (bif (bool true) (num 1) (num 2)))
           (constraint-set=?
            (set (=== (tx-expr (bif (bool true) (num 1) (num 2)))
                      (tx-expr (num 1)))
                 (=== (tx-expr (bif (bool true) (num 1) (num 2)))
                      (tx-expr (num 2)))
                 (=== (tx-expr (bool true)) (tx-type (t-bool)))
                 (=== (tx-expr (num 1)) (tx-type (t-num)))
                 (=== (tx-expr (num 2)) (tx-type (t-num))))))

;; iszero
(test/pred (generate-constraints (iszero (id 'a)))
           (constraint-set=?
            (set (=== (tx-expr (iszero (id 'a))) (tx-type (t-bool)))
                 (=== (tx-expr (id 'a)) (tx-type (t-num))))))

;; list ops
(test/pred (generate-constraints (tempty))
           (constraint-set=?
            (set (=== (tx-expr (tempty)) (tx-type (t-list (t-var (gensym))))))))

(test/pred (generate-constraints (istempty (id 'a)))
           (constraint-set=?
            (set (=== (tx-expr (istempty (id 'a))) (tx-type (t-bool)))
                 (=== (tx-expr (id 'a)) (tx-type (t-list (t-var (gensym))))))))

(test/pred (generate-constraints (tfirst (id 'a)))
           (constraint-set=?
            (set (=== (tx-expr (tfirst (id 'a))) (tx-type (t-var (gensym 'a))))
                 (=== (tx-expr (id 'a))
                      (tx-list (tx-expr (tfirst (id 'a))))))))

(test/pred (generate-constraints (trest (id 'a)))
           (constraint-set=?
            (set (=== (tx-expr (trest (id 'a)))
                      (tx-type (t-list (t-var (gensym 'a)))))
                 (=== (tx-expr (id 'a))
                      (tx-type (t-list (t-var (gensym 'a))))))))

(test/pred (generate-constraints (tcons (id 'a) (id 'b)))
           (constraint-set=?
            (set (=== (tx-expr (tcons (id 'a) (id 'b)))
                      (tx-list (tx-expr (id 'a))))
                 (=== (tx-expr (id 'b)) (tx-list (tx-expr (id 'a)))))))
(test/pred (generate-constraints (tcons (num 1) (tempty)))
           (constraint-set=?
            (set (=== (tx-expr (num 1)) (tx-type (t-num)))
                 (=== (tx-expr (tempty)) (tx-list (tx-expr (num 1))))
                 (=== (tx-expr (tcons (num 1) (tempty)))
                               (tx-list (tx-expr (num 1)))))))

;; Unification tests

(test/pred ((replace (--> (id 'a) (tx-type (t-num))))
                    (=== (tx-expr (id 'a)) (tx-expr (id 'b))))
           (constraint=? (=== (tx-type (t-num)) (tx-expr (id 'b)))))
(test/pred ((replace (--> (id 'x) (tx-type (t-num))))
                    (=== (tx-expr (id 'a)) (tx-expr (id 'b))))
           (constraint=? (=== (tx-expr (id 'a)) (tx-expr (id 'b)))))