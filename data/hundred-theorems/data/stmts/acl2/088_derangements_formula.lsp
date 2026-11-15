;; Statement-only formalization of hundred-theorems corpus artifact
;; hundred-theorems__acl2__088, "Derangements Formula": for every nonempty
;; finite set, the number of fixed-point-free permutations is the nearest
;; integer to n! / e, with exp(-1) represented by its exact alternating
;; factorial-series approximants. This file contains no proof.

(in-package "ACL2")

;; A permutation is represented by its image list in the order of the
;; duplicate-free carrier list.
(defun ht088-prepend-to-each (value lists)
  (if (consp lists)
      (cons (cons value (car lists))
            (ht088-prepend-to-each value (cdr lists)))
    nil))

(defun ht088-insert-everywhere (value values)
  (declare (xargs :measure (acl2-count values)))
  (if (consp values)
      (cons (cons value values)
            (ht088-prepend-to-each
             (car values)
             (ht088-insert-everywhere value (cdr values))))
    (list (list value))))

(defun ht088-insert-into-each-permutation (value permutations)
  (if (consp permutations)
      (append
       (ht088-insert-everywhere value (car permutations))
       (ht088-insert-into-each-permutation
        value (cdr permutations)))
    nil))

(defun ht088-permutations (values)
  (if (consp values)
      (ht088-insert-into-each-permutation
       (car values)
       (ht088-permutations (cdr values)))
    (list nil)))

(defun ht088-fixed-point-free-p (carrier image)
  (if (consp carrier)
      (and (consp image)
           (not (equal (car carrier) (car image)))
           (ht088-fixed-point-free-p (cdr carrier) (cdr image)))
    (equal image nil)))

(defun ht088-filter-derangements (carrier permutations)
  (if (consp permutations)
      (if (ht088-fixed-point-free-p carrier (car permutations))
          (cons (car permutations)
                (ht088-filter-derangements
                 carrier (cdr permutations)))
        (ht088-filter-derangements carrier (cdr permutations)))
    nil))

(defun ht088-derangements (carrier)
  (ht088-filter-derangements
   carrier
   (ht088-permutations carrier)))

(defun ht088-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n (ht088-factorial (- n 1)))))

;; The value through index k is
;;   sum_{j=0}^k (-1)^j / j!.
(defun ht088-exp-minus-one-prefix-through (k)
  (declare (xargs :measure (nfix k)))
  (if (zp k)
      1
    (+ (ht088-exp-minus-one-prefix-through (- k 1))
       (/ (if (equal (mod k 2) 0) 1 -1)
          (ht088-factorial k)))))

(defun ht088-scaled-exp-minus-one-prefix (n k)
  (* (ht088-factorial n)
     (ht088-exp-minus-one-prefix-through k)))

;; Odd prefixes lie below exp(-1), even prefixes lie above it, and the two
;; selected prefixes form a nested rational enclosure of n! / e.  Requiring
;; that enclosure to lie in ROUNDED's half-open unit cell is the constructive
;; real-number encoding of ROUNDED = round(n! / e).
(defun ht088-rounds-factorial-over-e-p (n rounded)
  (let* ((lower-index (+ (* 2 n) 1))
         (upper-index (+ lower-index 1))
         (lower
          (ht088-scaled-exp-minus-one-prefix n lower-index))
         (upper
          (ht088-scaled-exp-minus-one-prefix n upper-index))
         (one-half (/ 1 2)))
    (and (natp n)
         (< 0 n)
         (integerp rounded)
         (<= (- rounded one-half) lower)
         (< upper (+ rounded one-half)))))

(defun hundred-theorems-088-derangements-formula-statement
    (n carrier)
  (implies
   (and (natp n)
        (< 0 n)
        (true-listp carrier)
        (no-duplicatesp-equal carrier)
        (equal (len carrier) n))
   (let* ((derangements (ht088-derangements carrier))
          (derangement-count (len derangements)))
     (and
      (true-listp derangements)
      (no-duplicatesp-equal derangements)
      (equal
       derangement-count
       (ht088-scaled-exp-minus-one-prefix n n))
      (ht088-rounds-factorial-over-e-p
       n derangement-count)))))

(value-triple :itpeval-statement-checked)
:q
