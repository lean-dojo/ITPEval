;; Statement-only formalization of PutnamBench corpus artifact putnam_1981_b4:
;; the assertion that every real linear subspace of 5-by-7 matrices containing
;; ranks 0, 1, 2, 4, and 5 also contains rank 3 is false. This file contains
;; no proof or counterexample construction.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Standard ACL2 has no primitive carrier for arbitrary real values. These
;; conservative interfaces describe a complete Archimedean ordered field,
;; hence the real field up to ordered-field isomorphism. Matrices are flat
;; row-major lists of 35 carrier elements.

(defstub putnam-1981-b4-real-p (real-type value) t)
(defstub putnam-1981-b4-zero (real-type) t)
(defstub putnam-1981-b4-one (real-type) t)
(defstub putnam-1981-b4-add (real-type left right) t)
(defstub putnam-1981-b4-mul (real-type left right) t)
(defstub putnam-1981-b4-neg (real-type value) t)
(defstub putnam-1981-b4-inv (real-type value) t)
(defstub putnam-1981-b4-less (real-type left right) t)
(defstub putnam-1981-b4-integer-embed (real-type value) t)
(defstub putnam-1981-b4-supremum (real-type set) t)

(defun putnam-1981-b4-leq (real-type left right)
  (not (putnam-1981-b4-less real-type right left)))

(defun putnam-1981-b4-real-set-member-p (set value)
  (if (apply$ set (list value)) t nil))

(defun-sk putnam-1981-b4-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (putnam-1981-b4-real-p real-type x)
      (putnam-1981-b4-real-p real-type y)
      (putnam-1981-b4-real-p real-type z))
     (let* ((zero (putnam-1981-b4-zero real-type))
            (one (putnam-1981-b4-one real-type))
            (x-plus-y (putnam-1981-b4-add real-type x y))
            (y-plus-z (putnam-1981-b4-add real-type y z))
            (x-times-y (putnam-1981-b4-mul real-type x y))
            (y-times-z (putnam-1981-b4-mul real-type y z))
            (minus-x (putnam-1981-b4-neg real-type x))
            (inverse-x (putnam-1981-b4-inv real-type x)))
       (and
        (putnam-1981-b4-real-p real-type x-plus-y)
        (putnam-1981-b4-real-p real-type x-times-y)
        (putnam-1981-b4-real-p real-type minus-x)
        (putnam-1981-b4-real-p real-type inverse-x)
        (equal
         (putnam-1981-b4-add real-type x-plus-y z)
         (putnam-1981-b4-add real-type x y-plus-z))
        (equal x-plus-y (putnam-1981-b4-add real-type y x))
        (equal (putnam-1981-b4-add real-type x zero) x)
        (equal (putnam-1981-b4-add real-type x minus-x) zero)
        (equal
         (putnam-1981-b4-mul real-type x-times-y z)
         (putnam-1981-b4-mul real-type x y-times-z))
        (equal x-times-y (putnam-1981-b4-mul real-type y x))
        (equal (putnam-1981-b4-mul real-type x one) x)
        (implies
         (equal x zero)
         (equal inverse-x zero))
        (implies
         (not (equal x zero))
         (equal
          (putnam-1981-b4-mul real-type x inverse-x)
          one))
        (equal
         (putnam-1981-b4-mul real-type x y-plus-z)
         (putnam-1981-b4-add
          real-type
          (putnam-1981-b4-mul real-type x y)
          (putnam-1981-b4-mul real-type x z))))))))

(defun-sk putnam-1981-b4-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (putnam-1981-b4-real-p real-type x)
      (putnam-1981-b4-real-p real-type y)
      (putnam-1981-b4-real-p real-type z))
     (let ((zero (putnam-1981-b4-zero real-type)))
       (and
        (not (putnam-1981-b4-less real-type x x))
        (or
         (putnam-1981-b4-less real-type x y)
         (equal x y)
         (putnam-1981-b4-less real-type y x))
        (implies
         (and
          (putnam-1981-b4-less real-type x y)
          (putnam-1981-b4-less real-type y z))
         (putnam-1981-b4-less real-type x z))
        (implies
         (putnam-1981-b4-less real-type x y)
         (putnam-1981-b4-less
          real-type
          (putnam-1981-b4-add real-type x z)
          (putnam-1981-b4-add real-type y z)))
        (implies
         (and
          (putnam-1981-b4-less real-type zero x)
          (putnam-1981-b4-less real-type zero y))
         (putnam-1981-b4-less
          real-type
          zero
          (putnam-1981-b4-mul real-type x y))))))))

(defun-sk putnam-1981-b4-integer-embedding-laws-p
    (real-type)
  (forall (m n)
    (implies
     (and (integerp m) (integerp n))
     (and
      (putnam-1981-b4-real-p
       real-type
       (putnam-1981-b4-integer-embed real-type m))
      (equal
       (putnam-1981-b4-integer-embed real-type (+ m n))
       (putnam-1981-b4-add
        real-type
        (putnam-1981-b4-integer-embed real-type m)
        (putnam-1981-b4-integer-embed real-type n)))
      (equal
       (putnam-1981-b4-integer-embed real-type (* m n))
       (putnam-1981-b4-mul
        real-type
        (putnam-1981-b4-integer-embed real-type m)
        (putnam-1981-b4-integer-embed real-type n)))
      (iff
       (< m n)
       (putnam-1981-b4-less
        real-type
        (putnam-1981-b4-integer-embed real-type m)
        (putnam-1981-b4-integer-embed real-type n)))))))

(defun-sk putnam-1981-b4-valid-real-set-p
    (real-type set)
  (forall (value)
    (implies
     (putnam-1981-b4-real-set-member-p set value)
     (putnam-1981-b4-real-p real-type value))))

(defun-sk putnam-1981-b4-upper-bound-p
    (real-type set upper)
  (forall (value)
    (implies
     (and
      (putnam-1981-b4-real-p real-type value)
      (putnam-1981-b4-real-set-member-p set value))
     (putnam-1981-b4-leq real-type value upper))))

(defun-sk putnam-1981-b4-real-set-nonempty-p
    (real-type set)
  (exists (value)
    (and
     (putnam-1981-b4-real-p real-type value)
     (putnam-1981-b4-real-set-member-p set value))))

(defun-sk putnam-1981-b4-real-set-bounded-p
    (real-type set)
  (exists (upper)
    (and
     (putnam-1981-b4-real-p real-type upper)
     (putnam-1981-b4-upper-bound-p
      real-type set upper))))

(defun-sk putnam-1981-b4-least-upper-bound-p
    (real-type set supremum)
  (forall (upper)
    (implies
     (and
      (putnam-1981-b4-real-p real-type upper)
      (putnam-1981-b4-upper-bound-p
       real-type set upper))
     (putnam-1981-b4-leq
      real-type supremum upper))))

(defun-sk putnam-1981-b4-completeness-p (real-type)
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (putnam-1981-b4-valid-real-set-p real-type set)
      (putnam-1981-b4-real-set-nonempty-p real-type set)
      (putnam-1981-b4-real-set-bounded-p real-type set))
     (let ((supremum
            (putnam-1981-b4-supremum real-type set)))
       (and
        (putnam-1981-b4-real-p real-type supremum)
        (putnam-1981-b4-upper-bound-p
         real-type set supremum)
        (putnam-1981-b4-least-upper-bound-p
         real-type set supremum))))))

(defun-sk putnam-1981-b4-archimedean-witness-p
    (real-type value)
  (exists (n)
    (and
     (natp n)
     (putnam-1981-b4-less
      real-type
      value
      (putnam-1981-b4-integer-embed real-type n)))))

(defun-sk putnam-1981-b4-archimedean-p (real-type)
  (forall (value)
    (implies
     (putnam-1981-b4-real-p real-type value)
     (putnam-1981-b4-archimedean-witness-p
      real-type value))))

(defun putnam-1981-b4-real-field-p (real-type)
  (let ((zero (putnam-1981-b4-zero real-type))
        (one (putnam-1981-b4-one real-type)))
    (and
     (putnam-1981-b4-real-p real-type zero)
     (putnam-1981-b4-real-p real-type one)
     (not (equal zero one))
     (putnam-1981-b4-field-laws-p real-type)
     (putnam-1981-b4-order-laws-p real-type)
     (putnam-1981-b4-less real-type zero one)
     (equal
      (putnam-1981-b4-integer-embed real-type 0)
      zero)
     (equal
      (putnam-1981-b4-integer-embed real-type 1)
      one)
     (putnam-1981-b4-integer-embedding-laws-p real-type)
     (putnam-1981-b4-completeness-p real-type)
     (putnam-1981-b4-archimedean-p real-type))))

;; Every subspace of the 35-dimensional matrix space has a finite spanning
;; list. Quantifying over all such lists is therefore equivalent to
;; quantifying over all real linear subspaces, without second-order set
;; parameters.

(defun putnam-1981-b4-real-list-p (real-type values)
  (if (consp values)
      (and
       (putnam-1981-b4-real-p real-type (car values))
       (putnam-1981-b4-real-list-p real-type (cdr values)))
    (equal values nil)))

(defun putnam-1981-b4-matrix-p (real-type matrix)
  (and
   (true-listp matrix)
   (equal (len matrix) 35)
   (putnam-1981-b4-real-list-p real-type matrix)))

(defun putnam-1981-b4-basis-p (real-type basis)
  (if (consp basis)
      (and
       (putnam-1981-b4-matrix-p real-type (car basis))
       (putnam-1981-b4-basis-p real-type (cdr basis)))
    (equal basis nil)))

(defun putnam-1981-b4-repeat (value count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons value
          (putnam-1981-b4-repeat value (- count 1)))))

(defun putnam-1981-b4-zero-matrix (real-type)
  (putnam-1981-b4-repeat
   (putnam-1981-b4-zero real-type)
   35))

(defun putnam-1981-b4-scale-matrix
    (real-type scalar matrix)
  (if (consp matrix)
      (cons
       (putnam-1981-b4-mul
        real-type scalar (car matrix))
       (putnam-1981-b4-scale-matrix
        real-type scalar (cdr matrix)))
    nil))

(defun putnam-1981-b4-add-matrices
    (real-type left right)
  (if (and (consp left) (consp right))
      (cons
       (putnam-1981-b4-add
        real-type (car left) (car right))
       (putnam-1981-b4-add-matrices
        real-type (cdr left) (cdr right)))
    nil))

(defun putnam-1981-b4-coefficients-p
    (real-type coefficients basis)
  (if (consp basis)
      (and
       (consp coefficients)
       (putnam-1981-b4-real-p
        real-type (car coefficients))
       (putnam-1981-b4-coefficients-p
        real-type (cdr coefficients) (cdr basis)))
    (equal coefficients nil)))

(defun putnam-1981-b4-linear-combination
    (real-type coefficients basis)
  (if (consp basis)
      (putnam-1981-b4-add-matrices
       real-type
       (putnam-1981-b4-scale-matrix
        real-type (car coefficients) (car basis))
       (putnam-1981-b4-linear-combination
        real-type (cdr coefficients) (cdr basis)))
    (putnam-1981-b4-zero-matrix real-type)))

;; Rank is the largest size of a nonzero minor, exactly as in the informal
;; problem. Rows and columns are selected by duplicate-free bounded lists.

(defun putnam-1981-b4-range-from (start count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons start
          (putnam-1981-b4-range-from
           (+ start 1) (- count 1)))))

(defun putnam-1981-b4-prefix-each (item lists)
  (if (consp lists)
      (cons
       (cons item (car lists))
       (putnam-1981-b4-prefix-each item (cdr lists)))
    nil))

(defun putnam-1981-b4-insert-everywhere (item values)
  (if (consp values)
      (cons
       (cons item values)
       (putnam-1981-b4-prefix-each
        (car values)
        (putnam-1981-b4-insert-everywhere
         item (cdr values))))
    (list (list item))))

(defun putnam-1981-b4-insert-into-each (item lists)
  (if (consp lists)
      (append
       (putnam-1981-b4-insert-everywhere
        item (car lists))
       (putnam-1981-b4-insert-into-each
        item (cdr lists)))
    nil))

(defun putnam-1981-b4-permutations (values)
  (if (consp values)
      (putnam-1981-b4-insert-into-each
       (car values)
       (putnam-1981-b4-permutations (cdr values)))
    (list nil)))

(defun putnam-1981-b4-count-greater (item values)
  (if (consp values)
      (+ (if (> item (car values)) 1 0)
         (putnam-1981-b4-count-greater
          item (cdr values)))
    0))

(defun putnam-1981-b4-inversion-count (permutation)
  (if (consp permutation)
      (+ (putnam-1981-b4-count-greater
          (car permutation) (cdr permutation))
         (putnam-1981-b4-inversion-count
          (cdr permutation)))
    0))

(defun putnam-1981-b4-minor-entries
    (matrix size rows columns index remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (let* ((minor-row (floor index size))
           (minor-column (mod index size))
           (source-row (nth minor-row rows))
           (source-column (nth minor-column columns)))
      (cons
       (nth (+ (* source-row 7) source-column) matrix)
       (putnam-1981-b4-minor-entries
        matrix size rows columns
        (+ index 1) (- remaining 1))))))

(defun putnam-1981-b4-diagonal-product
    (real-type matrix size permutation row)
  (if (consp permutation)
      (putnam-1981-b4-mul
       real-type
       (nth (+ (* row size) (car permutation)) matrix)
       (putnam-1981-b4-diagonal-product
        real-type matrix size (cdr permutation) (+ row 1)))
    (putnam-1981-b4-one real-type)))

(defun putnam-1981-b4-determinant-sum
    (real-type matrix size permutations)
  (if (consp permutations)
      (let* ((permutation (car permutations))
             (product
              (putnam-1981-b4-diagonal-product
               real-type matrix size permutation 0))
             (signed-product
              (if (evenp
                   (putnam-1981-b4-inversion-count permutation))
                  product
                (putnam-1981-b4-neg real-type product))))
        (putnam-1981-b4-add
         real-type
         signed-product
         (putnam-1981-b4-determinant-sum
          real-type matrix size (cdr permutations))))
    (putnam-1981-b4-zero real-type)))

(defun putnam-1981-b4-determinant
    (real-type matrix size)
  (putnam-1981-b4-determinant-sum
   real-type
   matrix
   size
   (putnam-1981-b4-permutations
    (putnam-1981-b4-range-from 0 size))))

(defun putnam-1981-b4-bounded-nat-list-p
    (values bound)
  (if (consp values)
      (and
       (natp (car values))
       (< (car values) bound)
       (putnam-1981-b4-bounded-nat-list-p
        (cdr values) bound))
    (equal values nil)))

(defun putnam-1981-b4-valid-selection-p
    (values bound size)
  (and
   (true-listp values)
   (equal (len values) size)
   (putnam-1981-b4-bounded-nat-list-p values bound)
   (no-duplicatesp-equal values)))

(defun-sk putnam-1981-b4-has-nonzero-minor-p
    (real-type matrix size)
  (exists (rows columns)
    (and
     (natp size)
     (<= size 5)
     (putnam-1981-b4-valid-selection-p rows 5 size)
     (putnam-1981-b4-valid-selection-p columns 7 size)
     (not
      (equal
       (putnam-1981-b4-determinant
        real-type
        (putnam-1981-b4-minor-entries
         matrix size rows columns 0 (* size size))
        size)
       (putnam-1981-b4-zero real-type))))))

(defun-sk putnam-1981-b4-no-larger-minor-p
    (real-type matrix rank-value)
  (forall (larger-size)
    (implies
     (and
      (natp larger-size)
      (< rank-value larger-size)
      (<= larger-size 5))
     (not
      (putnam-1981-b4-has-nonzero-minor-p
       real-type matrix larger-size)))))

(defun putnam-1981-b4-matrix-has-rank-p
    (real-type matrix rank-value)
  (and
   (putnam-1981-b4-matrix-p real-type matrix)
   (natp rank-value)
   (<= rank-value 5)
   (putnam-1981-b4-has-nonzero-minor-p
    real-type matrix rank-value)
   (putnam-1981-b4-no-larger-minor-p
    real-type matrix rank-value)))

(defun-sk putnam-1981-b4-span-contains-rank-p
    (real-type basis rank-value)
  (exists (coefficients)
    (and
     (putnam-1981-b4-coefficients-p
      real-type coefficients basis)
     (putnam-1981-b4-matrix-has-rank-p
      real-type
      (putnam-1981-b4-linear-combination
       real-type coefficients basis)
      rank-value))))

(defun-sk putnam-1981-b4-universal-assertion-p
    (real-type)
  (forall (basis)
    (implies
     (and
      (putnam-1981-b4-basis-p real-type basis)
      (putnam-1981-b4-span-contains-rank-p
       real-type basis 0)
      (putnam-1981-b4-span-contains-rank-p
       real-type basis 1)
      (putnam-1981-b4-span-contains-rank-p
       real-type basis 2)
      (putnam-1981-b4-span-contains-rank-p
       real-type basis 4)
      (putnam-1981-b4-span-contains-rank-p
       real-type basis 5))
     (putnam-1981-b4-span-contains-rank-p
      real-type basis 3))))

(defun putnambench-putnam-1981-b4-statement (real-type)
  (implies
   (putnam-1981-b4-real-field-p real-type)
   (iff
    (putnam-1981-b4-universal-assertion-p real-type)
    nil)))

(value-triple :itpeval-statement-checked)
:q
