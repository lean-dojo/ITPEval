;; Statement-only formalization of PutnamBench corpus artifact putnam_2025_a4:
;; the least dimension of 2025 real square matrices whose commuting pairs are
;; exactly the equal or cyclically adjacent indices is 3. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-gag-mode t)

;; The scalar symbols present an arbitrary real-closed ordered field. For each
;; of the dimensions 0, 1, 2, and 3, the matrix condition is a first-order
;; Boolean combination of finitely many polynomial equations over the prime
;; field. Tarski transfer therefore makes this statement equivalent to the
;; source statement over the real numbers without restricting matrix entries
;; to a countable family of syntactic Cauchy names.

(defstub p2025a4-scalar-p (x) t)
(defstub p2025a4-add-op (x y) t)
(defstub p2025a4-multiply-op (x y) t)
(defstub p2025a4-negate-op (x) t)
(defstub p2025a4-inverse-op (x) t)
(defstub p2025a4-less-op (x y) t)
(defstub p2025a4-zero () t)
(defstub p2025a4-one () t)

(defun p2025a4-add (x y)
  (p2025a4-add-op x y))

(defun p2025a4-multiply (x y)
  (p2025a4-multiply-op x y))

(defun p2025a4-negate (x)
  (p2025a4-negate-op x))

(defun p2025a4-inverse (x)
  (p2025a4-inverse-op x))

(defun p2025a4-less (x y)
  (if (p2025a4-less-op x y) t nil))

(defun p2025a4-subtract (x y)
  (p2025a4-add x (p2025a4-negate y)))

(defun-sk p2025a4-field-laws-p ()
  (forall (x y z)
    (implies
     (and
      (p2025a4-scalar-p x)
      (p2025a4-scalar-p y)
      (p2025a4-scalar-p z))
     (and
      (p2025a4-scalar-p (p2025a4-add x y))
      (p2025a4-scalar-p (p2025a4-multiply x y))
      (p2025a4-scalar-p (p2025a4-negate x))
      (implies
       (not (equal x (p2025a4-zero)))
       (p2025a4-scalar-p (p2025a4-inverse x)))
      (equal
       (p2025a4-add (p2025a4-add x y) z)
       (p2025a4-add x (p2025a4-add y z)))
      (equal
       (p2025a4-add x y)
       (p2025a4-add y x))
      (equal
       (p2025a4-add x (p2025a4-zero))
       x)
      (equal
       (p2025a4-add x (p2025a4-negate x))
       (p2025a4-zero))
      (equal
       (p2025a4-multiply
        (p2025a4-multiply x y) z)
       (p2025a4-multiply
        x (p2025a4-multiply y z)))
      (equal
       (p2025a4-multiply x y)
       (p2025a4-multiply y x))
      (equal
       (p2025a4-multiply x (p2025a4-one))
       x)
      (implies
       (not (equal x (p2025a4-zero)))
       (equal
        (p2025a4-multiply x (p2025a4-inverse x))
        (p2025a4-one)))
      (equal
       (p2025a4-multiply x (p2025a4-add y z))
       (p2025a4-add
        (p2025a4-multiply x y)
        (p2025a4-multiply x z)))))))

(defun-sk p2025a4-order-laws-p ()
  (forall (x y z)
    (implies
     (and
      (p2025a4-scalar-p x)
      (p2025a4-scalar-p y)
      (p2025a4-scalar-p z))
     (and
      (not (p2025a4-less x x))
      (or
       (equal x y)
       (p2025a4-less x y)
       (p2025a4-less y x))
      (implies
       (and
        (p2025a4-less x y)
        (p2025a4-less y z))
       (p2025a4-less x z))
      (implies
       (p2025a4-less x y)
       (p2025a4-less
        (p2025a4-add x z)
        (p2025a4-add y z)))
      (implies
       (and
        (p2025a4-less (p2025a4-zero) x)
        (p2025a4-less (p2025a4-zero) y))
       (p2025a4-less
        (p2025a4-zero)
        (p2025a4-multiply x y)))))))

(defun p2025a4-coefficient-list-p (coefficients)
  (if (consp coefficients)
      (and
       (p2025a4-scalar-p (car coefficients))
       (p2025a4-coefficient-list-p
        (cdr coefficients)))
    (equal coefficients nil)))

;; Coefficients use increasing degree order.
(defun p2025a4-polynomial-value (coefficients x)
  (if (consp coefficients)
      (p2025a4-add
       (car coefficients)
       (p2025a4-multiply
        x
        (p2025a4-polynomial-value
         (cdr coefficients) x)))
    (p2025a4-zero)))

(defun p2025a4-polynomial-p (coefficients)
  (and
   (true-listp coefficients)
   (p2025a4-coefficient-list-p coefficients)))

(defun p2025a4-odd-degree-polynomial-p (coefficients)
  (and
   (p2025a4-polynomial-p coefficients)
   (consp coefficients)
   (evenp (len coefficients))
   (not
    (equal
     (car (last coefficients))
     (p2025a4-zero)))))

(defun-sk p2025a4-square-root-exists-p (x)
  (exists (root)
    (and
     (p2025a4-scalar-p root)
     (equal
      (p2025a4-multiply root root)
      x))))

(defun-sk p2025a4-positive-square-roots-p ()
  (forall (x)
    (implies
     (and
      (p2025a4-scalar-p x)
      (p2025a4-less (p2025a4-zero) x))
     (p2025a4-square-root-exists-p x))))

(defun-sk p2025a4-polynomial-root-exists-p
    (coefficients)
  (exists (root)
    (and
     (p2025a4-scalar-p root)
     (equal
      (p2025a4-polynomial-value
       coefficients root)
      (p2025a4-zero)))))

(defun-sk p2025a4-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (p2025a4-odd-degree-polynomial-p coefficients)
     (p2025a4-polynomial-root-exists-p
      coefficients))))

(defun p2025a4-real-closed-field-p ()
  (and
   (p2025a4-scalar-p (p2025a4-zero))
   (p2025a4-scalar-p (p2025a4-one))
   (not (equal (p2025a4-zero) (p2025a4-one)))
   (p2025a4-less (p2025a4-zero) (p2025a4-one))
   (p2025a4-field-laws-p)
   (p2025a4-order-laws-p)
   (p2025a4-positive-square-roots-p)
   (p2025a4-odd-polynomial-roots-p)))

;; Matrices and matrix families are exact finite lists of carrier elements.

(defun p2025a4-row-p (row remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (equal row nil)
    (and
     (consp row)
     (p2025a4-scalar-p (car row))
     (p2025a4-row-p
      (cdr row) (- remaining 1)))))

(defun p2025a4-matrix-p (matrix k remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (equal matrix nil)
    (and
     (consp matrix)
     (p2025a4-row-p (car matrix) k)
     (p2025a4-matrix-p
      (cdr matrix) k (- remaining 1)))))

(defun p2025a4-family-p (family k remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (equal family nil)
    (and
     (consp family)
     (p2025a4-matrix-p (car family) k k)
     (p2025a4-family-p
      (cdr family) k (- remaining 1)))))

(defun p2025a4-entry
    (family matrix-index row column)
  (nth column
       (nth row
            (nth matrix-index family))))

(defun p2025a4-commutator-entry
    (family i j row column remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (p2025a4-zero)
    (let* ((middle (- remaining 1))
           (ir
            (p2025a4-entry family i row middle))
           (jc
            (p2025a4-entry family j middle column))
           (jr
            (p2025a4-entry family j row middle))
           (ic
            (p2025a4-entry family i middle column)))
      (p2025a4-add
       (p2025a4-subtract
        (p2025a4-multiply ir jc)
        (p2025a4-multiply jr ic))
       (p2025a4-commutator-entry
        family i j row column
        (- remaining 1))))))

(defun p2025a4-commute-columns-p
    (family k i j row remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      t
    (let ((column (- remaining 1)))
      (and
       (equal
        (p2025a4-commutator-entry
         family i j row column k)
        (p2025a4-zero))
       (p2025a4-commute-columns-p
        family k i j row (- remaining 1))))))

(defun p2025a4-commute-rows-p
    (family k i j remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      t
    (let ((row (- remaining 1)))
      (and
       (p2025a4-commute-columns-p
        family k i j row k)
       (p2025a4-commute-rows-p
        family k i j (- remaining 1))))))

(defun p2025a4-commute-p (family k i j)
  (p2025a4-commute-rows-p
   family k i j k))

(defun p2025a4-allowed-difference-p (difference)
  (or
   (equal difference 0)
   (equal difference 1)
   (equal difference 2024)))

(defun p2025a4-pair-condition-p
    (family k i j)
  (equal
   (if (p2025a4-commute-p family k i j)
       t nil)
   (if (p2025a4-allowed-difference-p (- j i))
       t nil)))

;; For a fixed i, remaining starts at 2025-i, so j ranges from i through 2024.

(defun p2025a4-family-condition-j-p
    (family k i remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      t
    (let ((j (- 2025 remaining)))
      (and
       (p2025a4-pair-condition-p family k i j)
       (p2025a4-family-condition-j-p
        family k i (- remaining 1))))))

(defun p2025a4-family-condition-i-p
    (family k remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      t
    (let ((i (- 2025 remaining)))
      (and
       (p2025a4-family-condition-j-p
        family k i remaining)
       (p2025a4-family-condition-i-p
        family k (- remaining 1))))))

(defun p2025a4-family-condition-p (family k)
  (p2025a4-family-condition-i-p
   family k 2025))

(defun-sk p2025a4-dimension-property-p (k)
  (exists (family)
    (and
     (natp k)
     (p2025a4-family-p family k 2025)
     (p2025a4-family-condition-p family k))))

(defun-sk p2025a4-three-is-lower-bound-p ()
  (forall (k)
    (implies
     (and
      (natp k)
      (< k 3))
     (not
      (p2025a4-dimension-property-p k)))))

(defun putnambench-putnam-2025-a4-statement ()
  (implies
   (p2025a4-real-closed-field-p)
   (and
    (p2025a4-dimension-property-p 3)
    (p2025a4-three-is-lower-bound-p))))

(value-triple :itpeval-statement-checked)
:q
