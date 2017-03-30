; Lati
(declare-const r0 Int)
(declare-const r1 Int)
(declare-const r2 Int)
(declare-const r3 Int)
(declare-const r4 Int)
(declare-const u0 Int)
(declare-const u1 Int)
(declare-const u2 Int)
(declare-const u3 Int)
(declare-const u4 Int)
(declare-const l0 Int)
(declare-const l1 Int)
(declare-const l2 Int)
(declare-const l3 Int)
(declare-const l4 Int)
(declare-const d0 Int)
(declare-const d1 Int)
(declare-const d2 Int)
(declare-const d3 Int)
(declare-const d4 Int)

; Grattacieli
(declare-fun rc (Int Int) Int)
; Definita 0 al di fuori di [0, ..., n-1]x[0, ..., n-1]
(assert (forall ((r Int) (c Int)) (=> (or (< r 0) (>= r 5)) (= (rc r c) 0))))
(assert (forall ((r Int) (c Int)) (=> (or (< c 0) (>= c 5)) (= (rc r c) 0))))

; Grattacieli compresi tra 1 e n
(assert (forall ((r Int) (c Int)) (=> (and (>= r 0) (< r 5) (>= c 0) (< c 5)) (and (> (rc r c) 0) (<= (rc r c) 5)))))
; Niente ripetizioni sulle righe
(assert (distinct (rc 0 0) (rc 0 1) (rc 0 2) (rc 0 3) (rc 0 4)))
(assert (distinct (rc 1 0) (rc 1 1) (rc 1 2) (rc 1 3) (rc 1 4)))
(assert (distinct (rc 2 0) (rc 2 1) (rc 2 2) (rc 2 3) (rc 2 4)))
(assert (distinct (rc 3 0) (rc 3 1) (rc 3 2) (rc 3 3) (rc 3 4)))
(assert (distinct (rc 4 0) (rc 4 1) (rc 4 2) (rc 4 3) (rc 4 4)))
; Niente ripetizioni sulle colonne
(assert (distinct (rc 0 0) (rc 1 0) (rc 2 0) (rc 3 0) (rc 4 0)))
(assert (distinct (rc 0 1) (rc 1 1) (rc 2 1) (rc 3 1) (rc 4 1)))
(assert (distinct (rc 0 2) (rc 1 2) (rc 2 2) (rc 3 2) (rc 4 2)))
(assert (distinct (rc 0 3) (rc 1 3) (rc 2 3) (rc 3 3) (rc 4 3)))
(assert (distinct (rc 0 4) (rc 1 4) (rc 2 4) (rc 3 4) (rc 4 4)))

; Functions
(define-fun max ((a Int) (b Int)) Int (ite (> a b) a b))

; Conta grattacieli visibili
(define-fun counter ((a0 Int) (a1 Int) (a2 Int) (a3 Int) (a4 Int)) Int
  (+ 1
     (ite (> a1 a0) 1 0)
     (ite (> a2 (max a1 a0)) 1 0)
     (ite (> a3 (max a2 (max a1 a0))) 1 0)
     (ite (> a4 (max a3 (max a2 (max a1 a0)))) 1 0)))

; Controlla che la griglia sia consistente
; Check right side
(assert (= r0 (counter (rc 0 4) (rc 0 3) (rc 0 2) (rc 0 1) (rc 0 0))))
(assert (= r1 (counter (rc 1 4) (rc 1 3) (rc 1 2) (rc 1 1) (rc 1 0))))
(assert (= r2 (counter (rc 2 4) (rc 2 3) (rc 2 2) (rc 2 1) (rc 2 0))))
(assert (= r3 (counter (rc 3 4) (rc 3 3) (rc 3 2) (rc 3 1) (rc 3 0))))
(assert (= r4 (counter (rc 4 4) (rc 4 3) (rc 4 2) (rc 4 1) (rc 4 0))))
; Check up side
(assert (= u0 (counter (rc 0 0) (rc 1 0) (rc 2 0) (rc 3 0) (rc 4 0))))
(assert (= u1 (counter (rc 0 1) (rc 1 1) (rc 2 1) (rc 3 1) (rc 4 1))))
(assert (= u2 (counter (rc 0 2) (rc 1 2) (rc 2 2) (rc 3 2) (rc 4 2))))
(assert (= u3 (counter (rc 0 3) (rc 1 3) (rc 2 3) (rc 3 3) (rc 4 3))))
(assert (= u4 (counter (rc 0 4) (rc 1 4) (rc 2 4) (rc 3 4) (rc 4 4))))
; Check left side
(assert (= l0 (counter (rc 0 0) (rc 0 1) (rc 0 2) (rc 0 3) (rc 0 4))))
(assert (= l1 (counter (rc 1 0) (rc 1 1) (rc 1 2) (rc 1 3) (rc 1 4))))
(assert (= l2 (counter (rc 2 0) (rc 2 1) (rc 2 2) (rc 2 3) (rc 2 4))))
(assert (= l3 (counter (rc 3 0) (rc 3 1) (rc 3 2) (rc 3 3) (rc 3 4))))
(assert (= l4 (counter (rc 4 0) (rc 4 1) (rc 4 2) (rc 4 3) (rc 4 4))))
; Check down side
(assert (= d0 (counter (rc 4 0) (rc 3 0) (rc 2 0) (rc 1 0) (rc 0 0))))
(assert (= d1 (counter (rc 4 1) (rc 3 1) (rc 2 1) (rc 1 1) (rc 0 1))))
(assert (= d2 (counter (rc 4 2) (rc 3 2) (rc 2 2) (rc 1 2) (rc 0 2))))
(assert (= d3 (counter (rc 4 3) (rc 3 3) (rc 2 3) (rc 1 3) (rc 0 3))))
(assert (= d4 (counter (rc 4 4) (rc 3 4) (rc 2 4) (rc 1 4) (rc 0 4))))

; Condizioni per la griglia
; Condizioni sui lati
(assert (= r2 2))
(assert (= u1 5))
(assert (= l1 3))
(assert (= d0 3))
(assert (= d3 4))
; Condizioni sui grattacieli
(assert (= (rc 4 3) 2))

(check-sat)
; (get-model)
