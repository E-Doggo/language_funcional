#lang play
(print-only-errors #f) ; Para ver solo los errores.

#|
<FAE> ::=   <num> | <bool> | <id>
            | (+ <FAE> <FAE>)
            | (- <FAE> <FAE>)
            | (if-tf <FAE> <FAE> <FAE>)
            | (with <id> <FAE> <FAE>)
            | (app <FAE> <FAE>) ; puedo aplicar una funcion a otra funcion / puedo usar una funcion como argumento. 
            | (fun <id> <FAE>) ; fun(que es una lambda) nombre-arg body
            ; cajas mutables
            | (newbox <expr>)
            | (setbox <expr> <expr>)
            | (openbox <expr>)
            | (seqn <expr> <expr>) ; esta es una secuencia el ; en C o begin en Scheme
|#

; Ejemplo de box
#|
{with {b {newbox 10}}
  {seqn
       {setbox b 20}
       {openbox b}}
}

{with {make-box {fun {x} {newbox x}}}
      {setbox {make-box 10} 20}
}

Ahi si hay problemas con los argumentos, podemos hacer el sistema de tipos. 
|#

(deftype Expr
  [num n]                                 ; <num>
  [bool b]                                ; <bool>
  [add l r]                               ; (+ <FAE> <FAE>)
  [sub l r]                               ; (- <FAE> <FAE>)
  [if-tf c et ef]                         ; (if-tf <FAE> <FAE> <FAE>)
  [with id-name named-expr body-expr]     ; (with <id> <FAE> <FAE>)
  [id name]                               ; <id> 
  [app fname arg-expr]                    ; (app <FAE> <FAE>) ; ahora podemos aplicar una funcion a otra
  [fun arg body]                          ; (fun <id> <FAE>) ; mantenemos el <id> como el nombre del argumento
  [newbox b]
  [openbox b]
  [setbox b n]
  [seqn h t]  ;concatenar para expresiones ilimitadas, como el foldr con seqn y '().
  [set id e]
) 


; 1. Actualizar el environment
#|
<env> ::= (mtEnv)
          | (aEnv <id> <loc> <env>)
|#
(deftype Env
  (mtEnv)
  (aEnv id loc env)
  )

; empty-env -> (mtEnv)
(define empty-env (mtEnv))

; extend-env:: <id> <loc> <env> -> <env>
(define extend-env aEnv)
; env-lookup :: <id> <loc> -> <val>
; buscar el valor de una variable dentro del ambiete
(define (env-lookup x env)
  (match env
    [(mtEnv) (error "undefined: " x)]
    [(aEnv id loc tail)(if (eq? id x) loc (env-lookup x tail))]
    )
  )


; 2. Crear el store
#|
<sto> ::= (mtSto)
          | (aSto <loc> <val> <sto>)
|#

(deftype Sto
  (mtSto)
  (aSto loc val sto)
  )

(define empty-sto (mtSto))

(define extend-sto aSto)

(define (delete-sto l sto)
   (match sto
    [(mtSto) sto]
    [(aSto loc val tail) (if (eq? l loc) tail (aSto loc val (delete-sto l tail)))]
    )
  )

(define (sto-lookup l sto)
  (match sto
    [(mtSto) (error "segmentation fault: " l)]
    [(aSto loc val tail) (if (eq? l loc) val (sto-lookup l tail))]
    )
  )
#|
    (seqn e1 e2 e3 e4)
    (seqn e1 (parse-seqn e2 e3 e4))
    (seqn e1 (seqn e2 (parse-seqn e3 e4)))
    (seqn e1 (seqn e2 (seqn e3 e4))))

    
    (seqn e1 (seqn e2 e3)))
    (seqn e1 (seqn e2 (seqn e3 e4))))
    (seqn e1 (seqn e2 (seqn e3 (seqn e4 e5))))
|#
(define (parse-seqn args)
  (cond
    [(empty? (cdr args)) (parse (car args))]
    [(list? args)(seqn (parse (car args)) (parse-seqn (cdr args)))]
  )
  )

; parse: Src -> Expr; parsea codigo fuente
(define (parse src)
  (match src
    [(? number?) (num src)]
    [(? boolean?) (bool src)]
    [(? symbol?) (id src)]
    [(list '+ s1 s2) (add (parse s1) (parse s2))]
    [(list '- s1 s2) (sub (parse s1) (parse s2))]
    [(list 'if-tf c et ef) (if-tf (parse c) (parse et) (parse ef))]
    [(list 'with (list x e) b) (app (fun x (parse b)) (parse e))]
    [(list 'newbox b) (newbox (parse b))]
    [(list 'openbox e) (openbox (parse e))]
    [(list 'setbox b v) (setbox (parse b) (parse v))]
    ;(seqn e1 e2)
    ;(seqn e1 e2 e3)
    ;(seqn e1 e2 e3 e4)
    [(list 'seqn h ...) (parse-seqn h)]
    #|
    (seqn e1 e2)
    (seqn e1 (seqn e2 e3)))
    (seqn e1 (seqn e2 (seqn e3 e4))))
    (seqn e1 (seqn e2 (seqn e3 (seqn e4 e5))))
    |#
    [(list 'set id e)(set id (parse e))]
    [(list arg e) (app (parse arg) (parse e))]
    [(list 'fun (list arg) body) (fun arg (parse body))]
    )
  )
; 4. Incluir un nuevo tipo de valor v*s
(deftype Val
  (valV v) ; numero, booleano, string, byte, etc.
  (closureV arg body env) ; closure = fun + env
  (v*s val sto) ; val (valV/closureV) + sto (last memory)
  (boxV loc)
  (voidV)
  )
; 3. Actualizar interp.
; Descubrimiento clave de la clase pasada: Sto necesita existir
; interp :: Expr Env Sto -> Val*Sto --> CÃ3mo represento este valor?
; interpreta una expresion
(define (interp expr env sto)
  (match expr
    [(num n) (v*s (valV n) sto)] ; 6. Actualizar valores basicos
    [(bool b) (v*s (valV b) sto)]
    [(fun arg body) (v*s (closureV arg body env) sto)]
    [(id x) (v*s (sto-lookup (env-lookup x env) sto) sto)] ; 7. Actualizar la busqueda de variables
    [(add l r) ; 8. Actualizar operaciones
     ; 1. Evaluar r con el sto actual
     (def (v*s r-val r-sto) (interp r env sto))
     ; 2. Evaluar l con el sto modificado por l
     (def (v*s l-val l-sto) (interp l env r-sto))
     ; 3. Evaluar la suma
     (v*s (valV+ l-val r-val) l-sto)]
   
    
    [(sub l r) ; 1. Evaluar l con el sto actual
     (def (v*s l-val l-sto) (interp l env sto))
     ; 2. Evaluar r con el sto modificado por l
     (def (v*s r-val r-sto) (interp r env l-sto))
     ; 3. Evaluar la resta
     (v*s (valV- l-val r-val) r-sto)]
    
    [(if-tf c et ef)
     (def (v*s c-val c-sto) (interp c env sto))
     (if (valV-v c-val)
         (interp et env c-sto)
         (interp ef env c-sto))]


    [(newbox b)
     (def new-loc (malloc sto))
     (def (v*s b-val b-sto) (interp b env sto))
     (v*s (boxV new-loc) (extend-sto new-loc b-val b-sto))
     ]

    [(openbox b)
     (def (v*s b-val b-sto) (interp b env sto))
     (v*s (sto-lookup (boxV-loc b-val) b-sto) b-sto)
     ]

    ;Ejercicio 3 Apoyo de Chris Rivero, Debatido con Cesar mendez
    [(setbox b n)
      (def (v*s (boxV loc) b-sto) (interp b env sto))
      (def (v*s n-val n-sto) (interp n env b-sto))
      (def new-storage (delete-sto loc n-sto))
      (v*s (boxV loc) (extend-sto loc n-val new-storage))]
    
    ; 9. Actualizar la aplicacion de funcion
    [(app f e) ; f -> fun-expr & e -> arg-expr
     (def (v*s (closureV arg body fenv) fun-sto) (interp f env sto))
     (def (v*s arg-val arg-sto) (interp e env fun-sto))
     (def new-loc (malloc arg-sto))
     (interp body
             (extend-env arg new-loc fenv)
             (extend-sto new-loc arg-val arg-sto))]
    ;(interp body (extend-env (interp e env) env)

    [(seqn e1 e2)
     (def (v*s e1-val e1-sto) (interp e1 env sto))
     (def (v*s e2-val e2-sto) (interp e2 env e1-sto))
     (v*s e2-val e2-sto)
     ]

    [(set id e)
     (def (v*s e-val e-sto) (interp e env sto))
     (v*s voidV (extend-sto (env-lookup id env) e-val e-sto))]
))

; malloc :: sto -> loc
; devuelve una nueva posicion de memoria en base a un sto dado
(define (malloc sto)
  (match sto
    [(mtSto) 0]
    [(aSto loc _ tail) (+ 1 (malloc tail))] ; usamos longitud de sto.
    )
  )

; valV+ : Val -> Val
(define (valV+ s1 s2)
  (valV (+ (valV-v s1) (valV-v s2)))
  )

(define (valV- s1 s2)
  (valV (- (valV-v s1) (valV-v s2)))
  )

; run: Src -> Src
; corre un programa
(define (run prog) ; 10. Actualizar match
  (def (v*s res r-sto) (interp (parse prog) empty-env empty-sto)) ;5. Actualizar arg run
    (match res
      [(valV v) v]
      [(closureV arg body env) res]
      [(boxV loc) res]
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
(test/exn (run '{f 10}) "undefined")
(test (run '{with {f {fun {x} {+ x x}}}{f 10}}) 20)
(test (run '{{fun {x} {+ x x}} 10}) 20)
(test (run '{with {add1 {fun {x} {+ x 1}}}{add1 {add1 {add1 10}}}}) 13)
(test (run '{with {add1 {fun {x} {+ x 1}}}
                  {with {foo {fun {x} {+ {add1 x} {add1 x}}}}
                        {foo 10}}}) 22)
(test (run '{with {add1 {fun {x} {+ x 1}}}
                  {with {foo {fun {f} {+ {f 10} {f 10}}}}
                        {foo add1}}}) 22)
(test (run '{{fun {x}{+ x 1}} {+ 2 3}}) 6)
(test (run '{with {apply10 {fun {f} {f 10}}}
                  {with {add1 {fun {x} {+ x 1}}}
                        {apply10 add1}}}) 11)


(test (run '{with {addN {fun {n}
                       {fun {x} {+ x n}}}}
            {{addN 10} 20}}) 30)

(run '{newbox 5})
(run '{openbox {newbox 5}})
(run '{setbox {newbox 5} 4})
(run '{openbox {setbox {newbox 5} 2}})


(test (run '{with {b {newbox 10}}
                  {seqn
                   {setbox b 20}
                   {openbox b}}}) 20)

(test (run '{with {b {newbox 10}}
  {seqn
       {setbox b {+ 1{openbox b}}}
       {openbox b}}
}) 11)

(test/exn (run '{with {a {newbox 0}}
            {seqn {with {b 3} b}
                  b}}) "undefined")

(test (run '{with {a {newbox 0}}
            {with {f {fun {x} {+ x {openbox a}}}}
                  {seqn
                   {setbox a 2}
                   {f 5}}}}) 7)

(run '{with {a 10}
            {with {f {fun {x} {+ x a}}}
                  {seqn
                   {set a 20}
                   {with {a 3}
                         {f 2}}}}})



; On left to right the awnser would be 32 due to first opening box when the value is 10 in sto and then opening the box after its been set to 22
; Making the operation + 10 22
#|
(test (run '{with {b {newbox 10}}
  {seqn
       {setbox b {+ {openbox b} {openbox {setbox b 22}}}}
       {openbox b}}
}) 32)
|#

; Meanwhile, on right to left the awnser would be 44 due to first opening the box after its been set to 22 on sto and then opening it once again 
; Making the operation + 22 22
(test (run '{with {b {newbox 10}}
  {seqn
       {setbox b {+ {openbox b} {openbox {setbox b 22}}}}
       {openbox b}}
}) 44)


;TEST CON SEQN N
(run '{with {b {newbox 10}}
                  {seqn
                   {setbox b 20}
                   {setbox b 30}
                   {openbox {setbox b {+ 3 5}}}
                   {setbox b 45}
                   {openbox b}
                   }})

