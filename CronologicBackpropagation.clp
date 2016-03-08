;;;;
;;;; hechos
;;;;

(deffacts datos
; numero de variables del problema
  (estructura 7)	

  ; dominios para cada variable
  (dominio 1 a b c d e f g) 
  (dominio 2 a b c d e f g) 
  (dominio 3 a b c d e f g)
  (dominio 4 a b c d e f g)
  (dominio 5 a b c d e f g)
  (dominio 6 a b c d e f g)
  (dominio 7 a b c d e f g)
  
;solucion
	(solucion))

;(deffacts informacion-control
;	(secuencia-fases avances restricciones))

; contador de soluciones encontradas
(defglobal ?*nsol* = 0) 

(deftemplate elementos
	(slot posicion
		(default 0)
		(type INTEGER))
	(slot elemento
		(default ?DERIVE)
		(type SYMBOL))
	(slot eliminado
		(default 0)
		(type INTEGER)))

;;;;
;;;; reglas
;;;;

(defrule inicio
	(declare (salience 10000))
	=>
	(assert (fase inicializacion)))
	
;;;; reglas inicializacion
(defrule genera-elemento-dominio
	(fase inicializacion)
	(dominio ?pos $? ?ele $?)
	=>
	(assert (elementos
				(posicion ?pos)
				(elemento ?ele)
				(eliminado 0))))
				
(defrule cambio-fase
	(declare (salience -10))
	?f <- (fase inicializacion)
	=>
	(retract ?f)
	(assert (fase avance)))

	
;;;; reglas avance
(defrule avanza
	(declare (salience 100))
	(fase avance)	
	?f <- (solucion $?a)
; quedan elementos para añadir en la siguiente posicion de la solucion (no han sido eliminados)
	(elementos 
		(elemento ?ele) ;buscamos un elemento
		(posicion ?b&:(= ?b (+ 1 (length$ ?a)))) ; del dominio siguiente
		(eliminado 0)) ; que este disponible
	=>
	(retract ?f)
	(assert (solucion $?a ?ele)))

; detecta que tenemos un dominio saturado.
(defrule detecta-dominio-saturado
	(declare (salience 300))
	(fase avance)	
	(solucion $?sol)
	(elementos
		(posicion ?b&:(= ?b (+ 1 (length$ ?sol))))) ; se corresponde con el siguiente dominio 
	(not (elementos
			(posicion ?b)
			(eliminado 0))) ; que no tenga disponibles
	=>
	(assert (vuelta-atras)))

; regla que comprueba si se ha alcanzado una solución
(defrule detecta-solucion
	(declare (salience 100))
	(fase avance)	
	?f <- (solucion $?a ?b)
	(estructura ?n&:(= (- ?n 1) (length$ ?a)))
	?h <- (elementos
		(elemento ?b)
		(posicion ?pos&:(= ?pos (+ 1 (length$ ?a))))
		)
	=>
	(bind ?*nsol* (+ 1 ?*nsol*))
	(printout t "Solucion " ?*nsol* " -> " (create$ $?a ?b) crlf)
	(modify ?h (eliminado 1))
	(assert (solucion $?a))
	(retract ?f))

;La aplicación acaba cuando se detecta que tenemos el dominio 1 saturado
(defrule fin
	(declare (salience 3000))
	?f <- (fase avance)
	(not (elementos 
			(posicion 1)
			(eliminado 0))) ; que no tenga disponibles
	=>
	(retract ?f)
	(printout t "Fin: " ?*nsol* crlf))
	
; Anula el ultimo valor  de la solución y libera la condición de vuelta-atrás
(defrule fin-vuelta-atras
	(declare (salience 350))
	(fase avance)	
	?f <- (vuelta-atras)
	?g <- (solucion $?inicio ?a)
	?h <- (elementos
			(posicion ?b&:(= ?b (+ 1 (length$ ?inicio))))
			(elemento ?a))
	=>
	(modify ?h (eliminado 1))
	(assert (solucion ?inicio))
	(retract ?f ?g))
	
; restaura valores de dominios
(defrule restaura-nivel
	(declare (salience 400))
	(fase avance)	
	(vuelta-atras)
	(solucion $?s)
	?f <- (elementos
				(posicion ?b&:(= ?b (+ 1 (length$ ?s))))
				(eliminado 1))
	=>
	(modify ?f (eliminado 0)))

	
;;;;
;;;; reglas restricciones
;;;;

;;;; no pueden haber dos elementos iguales en la solucion
(defrule test-restriccion1
	(declare (salience 200))
	(fase avance)
	(not (vuelta-atras))
	(solucion $?inicio ?ele $?medio ?ele) 
	?f <- (elementos
			(elemento ?ele)
			(posicion ?b&:(= ?b (+ 2 (length$ $?medio) (length$ $?inicio)))))
	=>
	(modify ?f (eliminado 1))
	(assert (vuelta-atras)))

;;;en la tercera posicion solo puede haber una c

(defrule jefe
        (declare (salience 201))
        (fase avance)
        (solucion ?a ?b ?p $?)
        (test (neq ?p c))
        ?f <- (elementos
			(elemento ?p)
                        (posicion 3)
                )
        =>
        (modify ?f (eliminado 1))
        (assert (vuelta-atras))
    
)
	
