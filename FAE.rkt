#lang play
(print-only-errors #f) ; Para ver solo los errores.

#|
<FAE> ::=   <num> | <bool> | <id>
            | (+ <FAE> <FAE>)
            | (- <FAE> <FAE>)
            | (zero?? <FAE>)
            | (if-tf <FAE> <FAE> <FAE>)
            | (with <id> <FAE> <FAE>)
            | (rec <id> <FAE> <FAE>)
            | (app <FAE> <FAE>) ; puedo aplicar una funcion a otra funcion / puedo usar una funcion como argumento. 
            | (fun <id> <FAE>) ; fun(que es una lambda) nombre-arg body

|#
(deftype Expr
  [num n]                                 ; <num>
  [bool b]                                ; <bool>
  [add l r]                               ; (+ <FAE> <FAE>)
  [sub l r]                               ; (- <FAE> <FAE>)
  [mult l r]
  [zero n]
  [if-tf c et ef]                         ; (if-tf <FAE> <FAE> <FAE>)
  [with id-name named-expr body-expr]     ; (with <id> <FAE> <FAE>)
  [rec id-name named-expr body-expr ]
  [id name]                               ; <id> 
  [app fname arg-expr]                    ; (app <FAE> <FAE>) ; ahora podemos aplicar una funcion a otra
  [fun arg body]                          ; (fun <id> <FAE>) ; mantenemos el <id> como el nombre del argumento
) 


#|
<env> ::= (mtEnv)
          | (aEnv <id> <val> <env>)
|#
(deftype Env
  (mtEnv)
  (aEnv id val env)
  (aRecEnv id b-val env)
  )

; empty-env -> (mtEnv)
(define empty-env (mtEnv))

; extend-env:: <id> <val> <env> -> <env>
(define extend-env aEnv)
; env-lookup :: <id> <env> -> <val>
; buscar el valor de una variable dentro del ambiete
(define (env-lookup x env)
  (match env
    [(mtEnv) (error "undefined: " x)]
    [(aEnv id val tail)(if (eq? id x) val (env-lookup x tail))]
    [(aRecEnv id val tail)(if (eq? id x) (unbox val) (env-lookup x tail))]
    )
  )

; parse: Src -> Expr
; parsea codigo fuente
(define (parse src)
  (match src
    [(? number?) (num src)]
    [(? boolean?) (bool src)]
    [(? symbol?) (id src)]
    [(list '+ s1 s2) (add (parse s1) (parse s2))]
    [(list '- s1 s2) (sub (parse s1) (parse s2))]
    [(list '* s1 s2) (mult (parse s1) (parse s2))]
    [(list 'zero?? n) (zero (parse n))]
    [(list 'if-tf c et ef) (if-tf (parse c) (parse et) (parse ef))]
    [(list 'with (list x e) b) (with x (parse e) (parse b))]
    [(list 'rec (list x e) b) (rec x (parse e) (parse b))]
    [(list arg e) (app (parse arg) (parse e))]; 2. Subir de nivel nuestras funciones
    [(list 'fun (list arg) body) (fun arg (parse body))] ; 1. Agregar el caso del fun
    )
  )

(deftype Val
  (valV v) ; numero, booleano, string, byte, etc.
  (closureV arg body env) ; closure = fun + env

  )

; interp :: Expr  Env -> Val
; interpreta una expresion
(define (interp expr env)
  (match expr
    [(num n) (valV n)]
    [(bool b) (valV b)]
    [(id x) (env-lookup x env)]; buscar el valor de x en env
    [(add l r) (valV+ (interp l env) (interp r env))]
    [(sub l r) (valV- (interp l env) (interp r env))]
    [(mult l r) (valV* (interp l env) (interp r env))]
    [(zero n) (zeroV (interp n env))]
    [(if-tf c et ef) (if (valV-v (interp c env))
                         (interp et env)
                         (interp ef env))]
    [(with x e b) (interp b (extend-env x (interp e env) env))] ; Si asociamos una funcion a una variable, la funcion entra al env
    [(fun arg body) (closureV arg body env)] ; Por ahora, devolvemos la misma expresion que nos llego
    [(app f e)
     (def (closureV arg body fenv) (interp f env)) ; Esto permite encontrar (fun 'x (add (id 'x) (id 'x))) por ejemplo y tomar arg y body
    
     (interp body (extend-env arg (interp e env) fenv))] ; parece que no funciona ni con estatico ni dinamico



     [(rec x ne b) (interp b (cyclic-env x ne env))]
  
))
; cyclic-env: ..... -> Env
(define (cyclic-env id ne env)
  ; 1 -> crear un ambiente temporal , incompeto y asociarlo A
  (def box-val (box #f))
  (def new-env (aRecEnv id box-val env))
  ; 2 -> interp ne en el ambiente temporal
  (def clos-val (interp ne new-env))
  ; 3 -> actualizar el ambiente temporal por el ambiente ciclico.
  (set-box! box-val clos-val)
  new-env
  )

; valV+ : Val -> Val
(define (valV+ s1 s2)
  (valV (+ (valV-v s1) (valV-v s2)))
  )

(define (valV* s1 s2)
  (valV (* (valV-v s1) (valV-v s2)))
  )

(define (valV- s1 s2)
  (valV (- (valV-v s1) (valV-v s2)))
  )

(define (zeroV n)
  (valV (eq? 0 (valV-v n))))

; run: Src -> Src
; corre un programa
(define (run prog)
  (let ([res (interp (parse prog) empty-env)])
    (match res
      [(valV v) v]
      [(closureV arg body env) res])
    )
  )

(test (run '{+ 3 4}) 7)
(test (run '{- 5 1}) 4)

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


; Adaptando las pruebas previas
;(test/exn (run '{f 10}) "undefined function") - el error partia de fundef-lookup
(test/exn (run '{f 10}) "undefined")

;(test (run '{f 10} (list '{define {f x} {+ x x}})) 20)
; 1. Asociar la funcion a un identificador
(test (run '{with {f {fun {x} {+ x x}}}{f 10}}) 20)
; 2. Usar la funcion directamente, como un lambda
(test (run '{{fun {x} {+ x x}} 10}) 20)

;(test (run '{add1 {add1 {add1 10}}}(list '{define {add1 x} {+ x 1}})) 13)
(test (run '{with {add1 {fun {x} {+ x 1}}}{add1 {add1 {add1 10}}}}) 13)

; Prueba fallida
(test (run '{with {add1 {fun {x} {+ x 1}}}
                  {with {foo {fun {x} {+ {add1 x} {add1 x}}}}
                        {foo 10}}}) 22)

(test (run '{with {add1 {fun {x} {+ x 1}}}
                  {with {foo {fun {f} {+ {f 10} {f 10}}}}
                        {foo add1}}}) 22)


; Pruebas para casos basicos
(test (run '{{fun {x}{+ x 1}} {+ 2 3}}) 6)
(test (run '{with {apply10 {fun {f} {f 10}}}
                  {with {add1 {fun {x} {+ x 1}}}
                        {apply10 add1}}}) 11)


(test (run '{with {addN {fun {n}
                       {fun {x} {+ x n}}}}
            {{addN 10} 20}}) 30)



(run '{rec {sum {fun {n}
                      {if-tf {zero?? n}
                             0
                             {+ n {sum {- n 1}}}
                             }
                      }
                 }
            {sum 6}
            })

(run '{rec {sum {fun {n}
                      {if-tf {zero?? n}
                             0
                             {+ n {sum {- n 1}}}
                             }
                      }
                 }
            {sum 6}
            })


(run '{rec {mult {fun {n}
                      {if-tf {zero?? n}
                             1
                             {* n {mult {- n 1}}}
                             }
                      }
                 }
            {mult 6}
            })

(run '{with {sum {fun {sum}
                      {fun {n}
                           {if-tf {zero?? n}
                                  0
                                  {+ n {{sum sum} {- n 1}}}}}}}
            {{sum sum} 10}})


(run '{with {Y {fun {f}
                      {with {h {fun {g}
                                    {fun {n}
                                         {{f {g g}} n}}}}
                            {h h}}}}
         {with {sum {Y {fun {sum}
                        {fun {n}
                             {if-tf {zero?? n}
                                    0
                                    {+ n {sum {- n 1}}}}}}}}
              {sum 10}}})
                        