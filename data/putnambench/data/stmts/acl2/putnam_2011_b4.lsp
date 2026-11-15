;; Statement-only formalization of PutnamBench corpus artifact putnam_2011_b4:
;; for every 2011-player, 2011-game Boolean outcome table, the determinant of
;; the standings matrix T+iW is a nonnegative integer divisible by 2^2010.
;; This file contains no proof.

(in-package "ACL2")

;; Since both source index types are Fin 2011, an exact 2011-by-2011 Boolean
;; table is the extensional representation of the source function games.

(defun putnam-2011-b4-boolean-p (value)
  (or (equal value t)
      (equal value nil)))

(defun putnam-2011-b4-boolean-row-p (row columns)
  (declare (xargs :measure (nfix columns)))
  (if (zp columns)
      (equal row nil)
    (and (consp row)
         (putnam-2011-b4-boolean-p (car row))
         (putnam-2011-b4-boolean-row-p
          (cdr row) (- columns 1)))))

(defun putnam-2011-b4-games-p (games rows columns)
  (declare (xargs :measure (nfix rows)))
  (if (zp rows)
      (equal games nil)
    (and (consp games)
         (putnam-2011-b4-boolean-row-p
          (car games) columns)
         (putnam-2011-b4-games-p
          (cdr games) (- rows 1) columns))))

;; Gaussian integers are represented extensionally as (real-part . imag-part).

(defun putnam-2011-b4-gaussian-add (left right)
  (cons (+ (car left) (car right))
        (+ (cdr left) (cdr right))))

(defun putnam-2011-b4-gaussian-neg (value)
  (cons (- (car value))
        (- (cdr value))))

(defun putnam-2011-b4-gaussian-mul (left right)
  (cons (- (* (car left) (car right))
           (* (cdr left) (cdr right)))
        (+ (* (car left) (cdr right))
           (* (cdr left) (car right)))))

;; Each matrix entry is (T_hk . W_hk), hence represents T_hk+iW_hk.

(defun putnam-2011-b4-entry (games player-h player-k)
  (if (consp games)
      (let ((h-won (nth player-h (car games)))
            (k-won (nth player-k (car games))))
        (putnam-2011-b4-gaussian-add
         (putnam-2011-b4-entry
          (cdr games) player-h player-k)
         (cons
          (if (equal h-won k-won) 1 0)
          (cond ((and h-won (not k-won)) 1)
                ((and (not h-won) k-won) -1)
                (t 0)))))
    (cons 0 0)))

(defun putnam-2011-b4-matrix-row
    (games player-h player-k columns)
  (declare (xargs :measure (nfix columns)))
  (if (zp columns)
      nil
    (cons
     (putnam-2011-b4-entry games player-h player-k)
     (putnam-2011-b4-matrix-row
      games player-h (+ player-k 1) (- columns 1)))))

(defun putnam-2011-b4-matrix
    (games player-h rows columns)
  (declare (xargs :measure (nfix rows)))
  (if (zp rows)
      nil
    (cons
     (putnam-2011-b4-matrix-row games player-h 0 columns)
     (putnam-2011-b4-matrix
      games (+ player-h 1) (- rows 1) columns))))

;; The determinant is the usual signed sum over all permutations.

(defun putnam-2011-b4-range-from (start count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons start
          (putnam-2011-b4-range-from
           (+ start 1) (- count 1)))))

(defun putnam-2011-b4-prefix-each (item lists)
  (if (consp lists)
      (cons
       (cons item (car lists))
       (putnam-2011-b4-prefix-each item (cdr lists)))
    nil))

(defun putnam-2011-b4-insert-everywhere (item list)
  (if (consp list)
      (cons
       (cons item list)
       (putnam-2011-b4-prefix-each
        (car list)
        (putnam-2011-b4-insert-everywhere
         item (cdr list))))
    (list (list item))))

(defun putnam-2011-b4-insert-into-each (item lists)
  (if (consp lists)
      (append
       (putnam-2011-b4-insert-everywhere item (car lists))
       (putnam-2011-b4-insert-into-each item (cdr lists)))
    nil))

(defun putnam-2011-b4-permutations (list)
  (if (consp list)
      (putnam-2011-b4-insert-into-each
       (car list)
       (putnam-2011-b4-permutations (cdr list)))
    (list nil)))

(defun putnam-2011-b4-count-greater (item list)
  (if (consp list)
      (+ (if (> item (car list)) 1 0)
         (putnam-2011-b4-count-greater item (cdr list)))
    0))

(defun putnam-2011-b4-inversion-count (permutation)
  (if (consp permutation)
      (+ (putnam-2011-b4-count-greater
          (car permutation) (cdr permutation))
         (putnam-2011-b4-inversion-count
          (cdr permutation)))
    0))

(defun putnam-2011-b4-diagonal-product
    (matrix permutation row)
  (if (consp permutation)
      (putnam-2011-b4-gaussian-mul
       (nth (car permutation) (nth row matrix))
       (putnam-2011-b4-diagonal-product
        matrix (cdr permutation) (+ row 1)))
    (cons 1 0)))

(defun putnam-2011-b4-determinant-sum
    (matrix permutations)
  (if (consp permutations)
      (let* ((permutation (car permutations))
             (product
              (putnam-2011-b4-diagonal-product
               matrix permutation 0))
             (signed-product
              (if (evenp
                   (putnam-2011-b4-inversion-count permutation))
                  product
                (putnam-2011-b4-gaussian-neg product))))
        (putnam-2011-b4-gaussian-add
         signed-product
         (putnam-2011-b4-determinant-sum
          matrix (cdr permutations))))
    (cons 0 0)))

(defun putnam-2011-b4-determinant (matrix dimension)
  (putnam-2011-b4-determinant-sum
   matrix
   (putnam-2011-b4-permutations
    (putnam-2011-b4-range-from 0 dimension))))

;; A complex Gaussian integer equals some natural n exactly when its imaginary
;; part is zero and its real part is a natural. The source existential witness
;; can therefore be eliminated without changing its quantifier scope.

(defun putnambench-putnam-2011-b4-statement (games)
  (implies
   (putnam-2011-b4-games-p games 2011 2011)
   (let ((determinant
          (putnam-2011-b4-determinant
           (putnam-2011-b4-matrix games 0 2011 2011)
           2011)))
     (and
      (equal (cdr determinant) 0)
      (natp (car determinant))
      (equal
       (mod (car determinant) (expt 2 2010))
       0)))))

(value-triple :itpeval-statement-checked)
:q
