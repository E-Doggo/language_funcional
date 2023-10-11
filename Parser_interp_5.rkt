#lang play
(print-only-errors #f)
#|
<FAE> ::= <num> | <bool>
        | (+ <FAE> <FAE>)
        | (- <FAE> <FAE>)
        | (gt n1 n2)
        | (lt n1 n2)
        | (if-tf <FAE> <FAE> <FAE>)
        | (with id-name named-expr body-expr)
        | <id>
        | (app <id> <FAE>)
        | (fun <id> <FAE>)
|#
; (foo 4)-> {app 'foo      (num 4)}
;                 fun-name arg
(deftype Expr
  [num n]                                 ; <num>
  [bool b]                                ; <bool>
  [add l r]                               ; (+ <FAE> <FAE>)
  [sub l r]                               ; (- <FAE> <FAE>)
  [gt l r]
  [lt l r]
  [if-tf c et ef]                         ; (if-tf <FAE> <FAE> <FAE>)
  ;[with id-name named-expr body-expr]     ; (with <id> <FAE> <FAE>)
  [id name]                               ; <id> 
  [app fname arg-expr]                    ; (app <id> <FAE>)
  [fun arg body]
  [prim name args]
)

(define primitives
  (list (cons '+ +)
        (cons '- -))
  )

;(apply (car (assq '+ primitives)) '(1 2 3 4))
  
(deftype Val
  (valV v)
  (closureV arg body env) ;closure = fun + env
  (promiseV expr env) ;promise = expr + env
  )

#|
<env> ::= (mtEnv)
          | (aEnv <id> <val> <env>)
|#
(deftype Env
  (mtEnv)
  (aEnv id val env)
  )

; empty-env -> (mtEnv)
(define empty-env (mtEnv))

; extend-env:: <id> <val> <env> -> <env>
(define extend-env aEnv)

; env-lookup :: <id> <env> -> <val>
; buscar el valor de una variable dentro del ambiente
(define (env-lookup x env)
  (match env
    [(mtEnv) (error "undefined: " x)]
    [(aEnv id val en) (if(eq? x id) val (env-lookup x en))]
    )
  )

;(test (run env-lookup 'y (('x 1 ('y 4 (mtEnv)))) ) 4)
; parse: Src -> Expr
; parsea codigo fuente
(define (parse src)
  (match src
    [(? number?) (num src)]
    [(? boolean?) (bool src)]
    [(? symbol?) (id src)]
    [(list 'gt l r) (gt (parse l) (parse r))]
    [(list 'lt l r) (lt (parse l) (parse r))]
    [(list 'if-tf c et ef) (if-tf (parse c) (parse et) (parse ef))]
    [(list 'with (list id-name named-exp) body) (app (fun id-name (parse body)) (parse named-exp))]
    [(list 'fun (list x) body) (fun x (parse body))]
    [(list f arg) (app (parse f) (parse arg))]
    [(cons prim-name args)(prim prim-name (map parse args))]
    )
  )

;prim-ops: name args -> val
(define (prim-ops name args)
  (let ([vals (map (λ (x) (valV-v x)) args)])
    (valV (apply (cdr (assq name primitives)) vals ))
    )
  )

; interp :: Expr Env -> val
; interpreta una expresion
(define (interp expr env)
  (match expr
    [(num n) (valV n)]
    [(bool b) (valV b)]
    [(id x) (env-lookup x env)]; busca el valor de x en env
    [(add l r) (valV+ (strict (interp l env)) (strict (interp r env)))]
    [(sub l r) (valV- (strict (interp l env)) (strict (interp r env)))]
    [(gt l r) (> (strict (interp l env)) (strict (interp r env)))]
    [(lt l r) (< (strict (interp l env)) (strict (interp r env)))]
    [(prim prim-name args)(prim-ops prim-name (map (λ (x) (strict (interp x env))) args))]
    [(if-tf c et ef) (if (strict (interp c env))(strict (interp et env))(strict (interp ef env)))]
    #|[(with x e b)
     (interp b (extend-env x (interp e env) env))]|#
    [(fun x body) (closureV x body env)]

    [(app f e)
     (def (closureV arg body fenv) (strict (interp f env)))
     ;(interp body fundefs(extend-env arg (interp e fundefs env) env)); scope dinamico
     (interp body(extend-env arg 
                             (promiseV e env)
                             fenv)) ;scope statico
     ]
))

; valV :valV valV -> valV
(define (valV+ s1 s2)
  (valV (+ (valV-v s1) (valV-v s2)))
  )

(define (valV- s1 s2)
  (valV (- (valV-v s1) (valV-v s2)))
  )

;strict -> Val (valV/closureV/promiseV) -> Val(Valv/closureV)
;destructor de promesas o cumplidor de promesas
(define (strict val)
  (match val
    [(promiseV expr env)
     (begin
       (def interp-val (strict (interp expr env)))
       (printf "Forcing: ~a~n: " interp-val)
       interp-val)]
    [else val]
    )
  )


; run: Src list<fundef>? -> Expr
; corre un programa
(define (run prog)
  (let ([res (interp (parse prog) empty-env)])
    ;Un posible solucion
    ;interp env ...
    (match (strict res)
      [(valV v) v]
      [(closureV arg body env) res]
      ;[(promiseV expr env) (interp expr env)]
      ))
  )

;(run '{with {x 3} {with {y {+ 2 x}} {+ x y}}})
;(run '(with (x 3) (+ x 4)))
;(run '(lt 5 2))
(test (run '{- 5 1}) 4)

(test (run '{if-tf #t {+ 1 1} {- 1 1}}) 2)
(test (run '{if-tf #f {+ 1 1} {- 1 1}}) 0)
(test (run '{if-tf {+ 2 3} #t #f}) #t)
(test (run '{gt 1 2}) #f)
(test (run '{lt 1 2}) #t)
(test (run '{gt 4 2}) #t)
(test (run '{lt 5 2}) #f)
(test (run '{if-tf {lt 1 2} #t #f}) #t)
(test (run '{if-tf {gt 1 2} #t #f}) #f)


(test (run '{with {x 3} 2}) 2)
(test (run '{with {x 3} x}) 3)
(test (run '{with {x 3} {with {y 4} x}}) 3)
(test (run '{with {x 3} {+ x 4}}) 7)
(test (run '{with {x 3} {with {x 10} {+ x x}}}) 20)
(test (run '{with {x 3} {with {x x} {+ x x}}}) 6)
(test (run '{with {x 3} {with {y 2} {+ x y}}}) 5)
(test (run '{with {x 3} {+ 1 {with {y 2} {+ x y}}}}) 6)
(test (run '{with {x 3} {with {y {+ 2 x}} {+ x y}}}) 8)
(test (run '{with {x 3} {if-tf {+ x 1} {+ x 3} {+ x 9}}}) 6)

(run '{with {z {+ 2 2}}
              {with {y {+ z z}}
                    {with {x {+ y y}}
                          {+ x x}}}})

#|

(test/exn (run '{f 10}) "undefined function")
(test (run '{f 10} (list '{define {f x} {+ x x}})) 20)
(test (run '{add1 {add1 {add1 10}}} (list '{define {add1 x} {+ x 1}})) 13)
(run '{f 10} (list '{define {add1 x} {+ x 1}}'{define {f x} {+ {add1 x} {add1 x}}}))


;(run '{f 10} (list '{define {f x} {f x}}))

;(test (run env-lookup 'y (('x 1 ('y 4 (mtEnv))))) 4) corregir este test

;(run '{with {n 5} {f 10}})

|#