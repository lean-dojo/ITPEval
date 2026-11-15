;; Statement-only formalization of PutnamBench corpus artifact putnam_2023_b5:
;; positive integers whose every coprime multiplication permutation has a
;; permutation square root are exactly 1 and the integers congruent to 2
;; modulo 4. This file contains no proof.

(in-package "ACL2")

;; The residues 0,...,n-1 are the source carrier {1,...,n} modulo n, with n
;; represented by 0. A permutation is represented exactly by its image list
;; on these residues. For positive n, every integer m has one such residue,
;; and coprimality with n and the required congruences depend only on that
;; residue. Thus the finite searches below preserve both source quantifiers.

(defun putnam-2023-b5-residues (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons (- count 1)
          (putnam-2023-b5-residues (- count 1)))))

(defun putnam-2023-b5-prefix-each (item lists)
  (if (endp lists)
      nil
    (cons (cons item (car lists))
          (putnam-2023-b5-prefix-each item (cdr lists)))))

(defun putnam-2023-b5-insert-everywhere (item values)
  (if (endp values)
      (list (list item))
    (cons (cons item values)
          (putnam-2023-b5-prefix-each
           (car values)
           (putnam-2023-b5-insert-everywhere
            item (cdr values))))))

(defun putnam-2023-b5-insert-into-each (item permutations)
  (if (endp permutations)
      nil
    (append
     (putnam-2023-b5-insert-everywhere
      item (car permutations))
     (putnam-2023-b5-insert-into-each
      item (cdr permutations)))))

(defun putnam-2023-b5-permutations (values)
  (if (endp values)
      (list nil)
    (putnam-2023-b5-insert-into-each
     (car values)
     (putnam-2023-b5-permutations (cdr values)))))

(defun putnam-2023-b5-coprime-through-p
    (m n divisor)
  (declare (xargs :measure (nfix divisor)))
  (if (and (natp divisor)
           (< 1 divisor))
      (and
       (not
        (and (equal (mod m divisor) 0)
             (equal (mod n divisor) 0)))
       (putnam-2023-b5-coprime-through-p
        m n (- divisor 1)))
    t))

(defun putnam-2023-b5-coprime-p (m n)
  (and
   (natp m)
   (posp n)
   (putnam-2023-b5-coprime-through-p m n n)))

(defun putnam-2023-b5-square-congruences-p
    (permutation m n remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      t
    (let* ((k (- n remaining))
           (first-image (nth k permutation))
           (second-image (nth first-image permutation)))
      (and
       (equal second-image (mod (* m k) n))
       (putnam-2023-b5-square-congruences-p
        permutation m n (- remaining 1))))))

(defun putnam-2023-b5-has-square-root-p
    (permutations m n)
  (if (endp permutations)
      nil
    (or
     (putnam-2023-b5-square-congruences-p
      (car permutations) m n n)
     (putnam-2023-b5-has-square-root-p
      (cdr permutations) m n))))

(defun putnam-2023-b5-all-multipliers-p
    (count n permutations)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      t
    (let ((m (- count 1)))
      (and
       (or
        (not (putnam-2023-b5-coprime-p m n))
        (putnam-2023-b5-has-square-root-p
         permutations m n))
       (putnam-2023-b5-all-multipliers-p
        (- count 1) n permutations)))))

(defun putnam-2023-b5-property-p (n)
  (and
   (posp n)
   (let ((permutations
          (putnam-2023-b5-permutations
           (putnam-2023-b5-residues n))))
     (putnam-2023-b5-all-multipliers-p
      n n permutations))))

(defun putnam-2023-b5-solution-p (n)
  (and
   (natp n)
   (or (equal n 1)
       (equal (mod n 4) 2))))

(defun putnambench-putnam-2023-b5-statement (n)
  (implies
   (natp n)
   (equal
    (putnam-2023-b5-property-p n)
    (putnam-2023-b5-solution-p n))))

(value-triple :itpeval-statement-checked)
:q
