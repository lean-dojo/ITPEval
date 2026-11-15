;; Statement-only formalization of thousand-theorems corpus artifact Q17005116,
;; "Birkhoff's representation theorem": the canonical map from a finite
;; distributive lattice to the powerset of its sup-irreducible elements is an
;; injective lattice homomorphism. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A duplicate-free carrier list presents the source Fintype. Total operation
;; tables present meet and join extensionally on that carrier. The equational
;; lattice axioms induce exactly the source order, with x <= y iff x meet y = x.

(defun q17005116-table-value (x y table)
  (cdr (assoc-equal (list x y) table)))

(defun q17005116-op-row-total-p (x ys carrier table)
  (if (endp ys)
      t
    (let ((entry (assoc-equal (list x (car ys)) table)))
      (and
       (consp entry)
       (member-equal (cdr entry) carrier)
       (q17005116-op-row-total-p
        x (cdr ys) carrier table)))))

(defun q17005116-op-total-p (xs carrier table)
  (if (endp xs)
      t
    (and
     (q17005116-op-row-total-p
      (car xs) carrier carrier table)
     (q17005116-op-total-p
      (cdr xs) carrier table))))

(defun q17005116-commutative-row-p (x ys table)
  (if (endp ys)
      t
    (and
     (equal
      (q17005116-table-value x (car ys) table)
      (q17005116-table-value (car ys) x table))
     (q17005116-commutative-row-p
      x (cdr ys) table))))

(defun q17005116-commutative-p (xs carrier table)
  (if (endp xs)
      t
    (and
     (q17005116-commutative-row-p
      (car xs) carrier table)
     (q17005116-commutative-p
      (cdr xs) carrier table))))

(defun q17005116-associative-third-p (x y zs table)
  (if (endp zs)
      t
    (let ((z (car zs)))
      (and
       (equal
        (q17005116-table-value
         (q17005116-table-value x y table)
         z
         table)
        (q17005116-table-value
         x
         (q17005116-table-value y z table)
         table))
       (q17005116-associative-third-p
        x y (cdr zs) table)))))

(defun q17005116-associative-second-p
    (x ys carrier table)
  (if (endp ys)
      t
    (and
     (q17005116-associative-third-p
      x (car ys) carrier table)
     (q17005116-associative-second-p
      x (cdr ys) carrier table))))

(defun q17005116-associative-p (xs carrier table)
  (if (endp xs)
      t
    (and
     (q17005116-associative-second-p
      (car xs) carrier carrier table)
     (q17005116-associative-p
      (cdr xs) carrier table))))

(defun q17005116-absorption-row-p
    (x ys meet-table join-table)
  (if (endp ys)
      t
    (let* ((y (car ys))
           (meet-xy
            (q17005116-table-value x y meet-table))
           (join-xy
            (q17005116-table-value x y join-table)))
      (and
       (equal
        (q17005116-table-value x join-xy meet-table)
        x)
       (equal
        (q17005116-table-value x meet-xy join-table)
        x)
       (q17005116-absorption-row-p
        x (cdr ys) meet-table join-table)))))

(defun q17005116-absorption-p
    (xs carrier meet-table join-table)
  (if (endp xs)
      t
    (and
     (q17005116-absorption-row-p
      (car xs) carrier meet-table join-table)
     (q17005116-absorption-p
      (cdr xs) carrier meet-table join-table))))

(defun q17005116-distributive-third-p
    (x y zs meet-table join-table)
  (if (endp zs)
      t
    (let ((z (car zs)))
      (and
       (equal
        (q17005116-table-value
         x
         (q17005116-table-value y z join-table)
         meet-table)
        (q17005116-table-value
         (q17005116-table-value x y meet-table)
         (q17005116-table-value x z meet-table)
         join-table))
       (q17005116-distributive-third-p
        x y (cdr zs) meet-table join-table)))))

(defun q17005116-distributive-second-p
    (x ys carrier meet-table join-table)
  (if (endp ys)
      t
    (and
     (q17005116-distributive-third-p
      x (car ys) carrier meet-table join-table)
     (q17005116-distributive-second-p
      x (cdr ys) carrier meet-table join-table))))

(defun q17005116-distributive-p
    (xs carrier meet-table join-table)
  (if (endp xs)
      t
    (and
     (q17005116-distributive-second-p
      (car xs) carrier carrier meet-table join-table)
     (q17005116-distributive-p
      (cdr xs) carrier meet-table join-table))))

(defun q17005116-finite-distributive-lattice-p
    (carrier meet-table join-table)
  (and
   (true-listp carrier)
   (no-duplicatesp-equal carrier)
   (alistp meet-table)
   (alistp join-table)
   (q17005116-op-total-p carrier carrier meet-table)
   (q17005116-op-total-p carrier carrier join-table)
   (q17005116-commutative-p
    carrier carrier meet-table)
   (q17005116-commutative-p
    carrier carrier join-table)
   (q17005116-associative-p
    carrier carrier meet-table)
   (q17005116-associative-p
    carrier carrier join-table)
   (q17005116-absorption-p
    carrier carrier meet-table join-table)
   (q17005116-distributive-p
    carrier carrier meet-table join-table)))

(defun q17005116-le-p (x y meet-table)
  (equal
   (q17005116-table-value x y meet-table)
   x))

;; This is Mathlib's SupIrred definition: the element is not minimal, and a
;; join equal to it has one operand equal to it.

(defun q17005116-minimal-p (x ys meet-table)
  (if (endp ys)
      t
    (and
     (implies
      (q17005116-le-p (car ys) x meet-table)
      (equal (car ys) x))
     (q17005116-minimal-p
      x (cdr ys) meet-table))))

(defun q17005116-sup-irred-third-p
    (x y zs join-table)
  (if (endp zs)
      t
    (let ((z (car zs)))
      (and
       (implies
        (equal
         (q17005116-table-value y z join-table)
         x)
        (or (equal y x)
            (equal z x)))
       (q17005116-sup-irred-third-p
        x y (cdr zs) join-table)))))

(defun q17005116-sup-irred-second-p
    (x ys carrier join-table)
  (if (endp ys)
      t
    (and
     (q17005116-sup-irred-third-p
      x (car ys) carrier join-table)
     (q17005116-sup-irred-second-p
      x (cdr ys) carrier join-table))))

(defun q17005116-sup-irred-p
    (x carrier meet-table join-table)
  (and
   (not
    (q17005116-minimal-p
     x carrier meet-table))
   (q17005116-sup-irred-second-p
    x carrier carrier join-table)))

;; The canonical Birkhoff set of x is the set of sup-irreducible j with j <= x.
;; Filtering the fixed carrier gives a canonical list for extensional set
;; equality and represents the full powerset of the finite subtype.

(defun q17005116-birkhoff-set
    (x remaining carrier meet-table join-table)
  (if (endp remaining)
      nil
    (let ((j (car remaining)))
      (if
       (and
        (q17005116-sup-irred-p
         j carrier meet-table join-table)
        (q17005116-le-p j x meet-table))
       (cons
        j
        (q17005116-birkhoff-set
         x (cdr remaining) carrier meet-table join-table))
       (q17005116-birkhoff-set
        x (cdr remaining) carrier meet-table join-table)))))

(defun q17005116-set-union-over
    (remaining left right)
  (if (endp remaining)
      nil
    (let ((x (car remaining)))
      (if (or (member-equal x left)
              (member-equal x right))
          (cons
           x
           (q17005116-set-union-over
            (cdr remaining) left right))
        (q17005116-set-union-over
         (cdr remaining) left right)))))

(defun q17005116-set-intersection-over
    (remaining left right)
  (if (endp remaining)
      nil
    (let ((x (car remaining)))
      (if (and (member-equal x left)
               (member-equal x right))
          (cons
           x
           (q17005116-set-intersection-over
            (cdr remaining) left right))
        (q17005116-set-intersection-over
         (cdr remaining) left right)))))

(defun q17005116-lattice-hom-row-p
    (x ys carrier meet-table join-table)
  (if (endp ys)
      t
    (let* ((y (car ys))
           (set-x
            (q17005116-birkhoff-set
             x carrier carrier meet-table join-table))
           (set-y
            (q17005116-birkhoff-set
             y carrier carrier meet-table join-table))
           (meet-xy
            (q17005116-table-value x y meet-table))
           (join-xy
            (q17005116-table-value x y join-table)))
      (and
       (equal
        (q17005116-birkhoff-set
         meet-xy carrier carrier meet-table join-table)
        (q17005116-set-intersection-over
         carrier set-x set-y))
       (equal
        (q17005116-birkhoff-set
         join-xy carrier carrier meet-table join-table)
        (q17005116-set-union-over
         carrier set-x set-y))
       (q17005116-lattice-hom-row-p
        x (cdr ys) carrier meet-table join-table)))))

(defun q17005116-lattice-hom-p
    (xs carrier meet-table join-table)
  (if (endp xs)
      t
    (and
     (q17005116-lattice-hom-row-p
      (car xs) carrier carrier meet-table join-table)
     (q17005116-lattice-hom-p
      (cdr xs) carrier meet-table join-table))))

(defun q17005116-injective-against-p
    (x ys carrier meet-table join-table)
  (if (endp ys)
      t
    (and
     (implies
      (equal
       (q17005116-birkhoff-set
        x carrier carrier meet-table join-table)
       (q17005116-birkhoff-set
        (car ys) carrier carrier meet-table join-table))
      (equal x (car ys)))
     (q17005116-injective-against-p
      x (cdr ys) carrier meet-table join-table))))

(defun q17005116-injective-p
    (xs carrier meet-table join-table)
  (if (endp xs)
      t
    (and
     (q17005116-injective-against-p
      (car xs) (cdr xs) carrier meet-table join-table)
     (q17005116-injective-p
      (cdr xs) carrier meet-table join-table))))

(defun thousand-theorems-q17005116-birkhoff-s-representation-theorem-statement
    (carrier meet-table join-table)
  (implies
   (q17005116-finite-distributive-lattice-p
    carrier meet-table join-table)
   (and
    (q17005116-lattice-hom-p
     carrier carrier meet-table join-table)
    (q17005116-injective-p
     carrier carrier meet-table join-table))))

(value-triple :itpeval-statement-checked)
:q
