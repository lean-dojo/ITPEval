;; Statement-only formalization of PutnamBench corpus artifact putnam_1996_a4:
;; a finite ternary orientation satisfying cyclic, reversal, and four-point
;; axioms admits an injective real ranking compatible with every increasing
;; triple. This file contains no proof.

(in-package "ACL2")

;; CARRIER is a duplicate-free enumeration of the arbitrary finite source
;; type, and RELATION is a duplicate-free enumeration of S. Thus the lists
;; represent the finite sets extensionally without restricting their elements.
;; The distinctness guards on the three structural axioms are the explicit,
;; non-vacuous formulation in the Lean source and in the mathematical problem.
;;
;; Every injective real-valued map on a finite carrier orders its elements by
;; increasing image. Conversely, any permutation of the carrier defines such
;; a map by assigning each element its integer position. Therefore the finite
;; permutation search below is bidirectionally equivalent to the source's
;; internal existential quantifier over g; no witness is an external parameter.

(defun putnam-1996-a4-set-list-p (values)
  (if (consp values)
      (and
       (not (member-equal (car values) (cdr values)))
       (putnam-1996-a4-set-list-p (cdr values)))
    (equal values nil)))

(defun putnam-1996-a4-triple-p (triple carrier)
  (and
   (true-listp triple)
   (equal (len triple) 3)
   (member-equal (car triple) carrier)
   (member-equal (cadr triple) carrier)
   (member-equal (caddr triple) carrier)))

(defun putnam-1996-a4-relation-p (relation carrier)
  (if (consp relation)
      (and
       (putnam-1996-a4-triple-p (car relation) carrier)
       (not (member-equal (car relation) (cdr relation)))
       (putnam-1996-a4-relation-p (cdr relation) carrier))
    (equal relation nil)))

(defun putnam-1996-a4-pairwise-distinct-3-p (a b c)
  (and
   (not (equal a b))
   (not (equal b c))
   (not (equal a c))))

(defun putnam-1996-a4-pairwise-distinct-4-p (a b c d)
  (and
   (not (equal a b))
   (not (equal a c))
   (not (equal a d))
   (not (equal b c))
   (not (equal b d))
   (not (equal c d))))

(defun putnam-1996-a4-relation-distinct-p (relation)
  (if (consp relation)
      (and
       (putnam-1996-a4-pairwise-distinct-3-p
        (caar relation)
        (cadar relation)
        (caddar relation))
       (putnam-1996-a4-relation-distinct-p (cdr relation)))
    t))

(defun putnam-1996-a4-in-s-p (a b c relation)
  (if (member-equal (list a b c) relation)
      t
    nil))

(defun putnam-1996-a4-cyclic-c-p (a b cs relation)
  (if (consp cs)
      (let ((c (car cs)))
        (and
         (implies
          (putnam-1996-a4-pairwise-distinct-3-p a b c)
          (iff
           (putnam-1996-a4-in-s-p a b c relation)
           (putnam-1996-a4-in-s-p b c a relation)))
         (putnam-1996-a4-cyclic-c-p
          a b (cdr cs) relation)))
    t))

(defun putnam-1996-a4-cyclic-b-p (a bs carrier relation)
  (if (consp bs)
      (and
       (putnam-1996-a4-cyclic-c-p
        a (car bs) carrier relation)
       (putnam-1996-a4-cyclic-b-p
        a (cdr bs) carrier relation))
    t))

(defun putnam-1996-a4-cyclic-p (as carrier relation)
  (if (consp as)
      (and
       (putnam-1996-a4-cyclic-b-p
        (car as) carrier carrier relation)
       (putnam-1996-a4-cyclic-p
        (cdr as) carrier relation))
    t))

(defun putnam-1996-a4-reversal-c-p (a b cs relation)
  (if (consp cs)
      (let ((c (car cs)))
        (and
         (implies
          (putnam-1996-a4-pairwise-distinct-3-p a b c)
          (iff
           (putnam-1996-a4-in-s-p a b c relation)
           (not
            (putnam-1996-a4-in-s-p c b a relation))))
         (putnam-1996-a4-reversal-c-p
          a b (cdr cs) relation)))
    t))

(defun putnam-1996-a4-reversal-b-p (a bs carrier relation)
  (if (consp bs)
      (and
       (putnam-1996-a4-reversal-c-p
        a (car bs) carrier relation)
       (putnam-1996-a4-reversal-b-p
        a (cdr bs) carrier relation))
    t))

(defun putnam-1996-a4-reversal-p (as carrier relation)
  (if (consp as)
      (and
       (putnam-1996-a4-reversal-b-p
        (car as) carrier carrier relation)
       (putnam-1996-a4-reversal-p
        (cdr as) carrier relation))
    t))

(defun putnam-1996-a4-four-point-d-p
    (a b c ds relation)
  (if (consp ds)
      (let ((d (car ds)))
        (and
         (implies
          (putnam-1996-a4-pairwise-distinct-4-p a b c d)
          (iff
           (and
            (putnam-1996-a4-in-s-p a b c relation)
            (putnam-1996-a4-in-s-p c d a relation))
           (and
            (putnam-1996-a4-in-s-p b c d relation)
            (putnam-1996-a4-in-s-p d a b relation))))
         (putnam-1996-a4-four-point-d-p
          a b c (cdr ds) relation)))
    t))

(defun putnam-1996-a4-four-point-c-p
    (a b cs carrier relation)
  (if (consp cs)
      (and
       (putnam-1996-a4-four-point-d-p
        a b (car cs) carrier relation)
       (putnam-1996-a4-four-point-c-p
        a b (cdr cs) carrier relation))
    t))

(defun putnam-1996-a4-four-point-b-p
    (a bs carrier relation)
  (if (consp bs)
      (and
       (putnam-1996-a4-four-point-c-p
        a (car bs) carrier carrier relation)
       (putnam-1996-a4-four-point-b-p
        a (cdr bs) carrier relation))
    t))

(defun putnam-1996-a4-four-point-p
    (as carrier relation)
  (if (consp as)
      (and
       (putnam-1996-a4-four-point-b-p
        (car as) carrier carrier relation)
       (putnam-1996-a4-four-point-p
        (cdr as) carrier relation))
    t))

(defun putnam-1996-a4-compatible-after-two-p
    (a b remaining relation)
  (if (consp remaining)
      (and
       (putnam-1996-a4-in-s-p
        a b (car remaining) relation)
       (putnam-1996-a4-compatible-after-two-p
        a b (cdr remaining) relation))
    t))

(defun putnam-1996-a4-compatible-after-one-p
    (a remaining relation)
  (if (consp remaining)
      (and
       (putnam-1996-a4-compatible-after-two-p
        a (car remaining) (cdr remaining) relation)
       (putnam-1996-a4-compatible-after-one-p
        a (cdr remaining) relation))
    t))

(defun putnam-1996-a4-compatible-order-p (order relation)
  (if (consp order)
      (and
       (putnam-1996-a4-compatible-after-one-p
        (car order) (cdr order) relation)
       (putnam-1996-a4-compatible-order-p
        (cdr order) relation))
    t))

(defun putnam-1996-a4-prepend-each (value lists)
  (if (endp lists)
      nil
    (cons
     (cons value (car lists))
     (putnam-1996-a4-prepend-each value (cdr lists)))))

(defun putnam-1996-a4-insert-everywhere (value values)
  (if (endp values)
      (list (list value))
    (cons
     (cons value values)
     (putnam-1996-a4-prepend-each
      (car values)
      (putnam-1996-a4-insert-everywhere
       value (cdr values))))))

(defun putnam-1996-a4-insert-into-permutations
    (value permutations)
  (if (endp permutations)
      nil
    (append
     (putnam-1996-a4-insert-everywhere
      value (car permutations))
     (putnam-1996-a4-insert-into-permutations
      value (cdr permutations)))))

(defun putnam-1996-a4-permutations (values)
  (if (endp values)
      (list nil)
    (putnam-1996-a4-insert-into-permutations
     (car values)
     (putnam-1996-a4-permutations (cdr values)))))

(defun putnam-1996-a4-compatible-order-exists-p
    (orders relation)
  (if (consp orders)
      (or
       (putnam-1996-a4-compatible-order-p
        (car orders) relation)
       (putnam-1996-a4-compatible-order-exists-p
        (cdr orders) relation))
    nil))

(defun putnambench-putnam-1996-a4-statement
    (carrier relation)
  (implies
   (and
    (putnam-1996-a4-set-list-p carrier)
    (putnam-1996-a4-relation-p relation carrier)
    (putnam-1996-a4-relation-distinct-p relation)
    (putnam-1996-a4-cyclic-p carrier carrier relation)
    (putnam-1996-a4-reversal-p carrier carrier relation)
    (putnam-1996-a4-four-point-p carrier carrier relation))
   (putnam-1996-a4-compatible-order-exists-p
    (putnam-1996-a4-permutations carrier)
    relation)))

(value-triple :itpeval-statement-checked)
:q
