;; Statement-only formalization of PutnamBench corpus artifact putnam_2023_b3:
;; the expected longest zigzag-subsequence length of independent uniform
;; samples from [0,1] is (2n+2)/3 for n at least 2. This file contains no proof.

(in-package "ACL2")

;; Outside the measure-zero set where two samples are equal, the zigzag
;; statistic depends only on the samples' relative order. Independence and
;; uniformity make all n! strict order types equiprobable. Thus the finite
;; average below is exactly the source expectation, not a restriction of its
;; real-valued sample space.

(defun putnam-2023-b3-indices (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons (- count 1)
          (putnam-2023-b3-indices (- count 1)))))

(defun putnam-2023-b3-prefix-each (item lists)
  (if (endp lists)
      nil
    (cons (cons item (car lists))
          (putnam-2023-b3-prefix-each item (cdr lists)))))

(defun putnam-2023-b3-insert-everywhere (item list)
  (if (endp list)
      (list (list item))
    (cons (cons item list)
          (putnam-2023-b3-prefix-each
           (car list)
           (putnam-2023-b3-insert-everywhere
            item (cdr list))))))

(defun putnam-2023-b3-insert-into-each (item lists)
  (if (endp lists)
      nil
    (append
     (putnam-2023-b3-insert-everywhere item (car lists))
     (putnam-2023-b3-insert-into-each item (cdr lists)))))

(defun putnam-2023-b3-permutations (list)
  (if (endp list)
      (list nil)
    (putnam-2023-b3-insert-into-each
     (car list)
     (putnam-2023-b3-permutations (cdr list)))))

;; These are exactly the index-preserving subsequences of LIST.

(defun putnam-2023-b3-subsequences (list)
  (if (endp list)
      (list nil)
    (let ((tail-subsequences
           (putnam-2023-b3-subsequences (cdr list))))
      (append
       tail-subsequences
       (putnam-2023-b3-prefix-each
        (car list) tail-subsequences)))))

(defun putnam-2023-b3-sign (value)
  (cond ((< value 0) -1)
        ((< 0 value) 1)
        (t 0)))

(defun putnam-2023-b3-alternating-differences-p
    (sequence previous-sign)
  (if (or (endp sequence)
          (endp (cdr sequence)))
      t
    (let ((current-sign
           (putnam-2023-b3-sign
            (- (cadr sequence) (car sequence)))))
      (and
       (not (equal current-sign 0))
       (or (equal previous-sign 0)
           (equal current-sign (- previous-sign)))
       (putnam-2023-b3-alternating-differences-p
        (cdr sequence) current-sign)))))

(defun putnam-2023-b3-zigzag-p (sequence)
  (and
   (consp sequence)
   (or
    (endp (cdr sequence))
    (putnam-2023-b3-alternating-differences-p
     sequence 0))))

(defun putnam-2023-b3-max (left right)
  (if (< left right) right left))

(defun putnam-2023-b3-longest-from-subsequences
    (subsequences)
  (if (endp subsequences)
      0
    (putnam-2023-b3-max
     (if (putnam-2023-b3-zigzag-p (car subsequences))
         (len (car subsequences))
       0)
     (putnam-2023-b3-longest-from-subsequences
      (cdr subsequences)))))

(defun putnam-2023-b3-longest-zigzag-length (permutation)
  (putnam-2023-b3-longest-from-subsequences
   (putnam-2023-b3-subsequences permutation)))

(defun putnam-2023-b3-sum-longest-lengths (permutations)
  (if (endp permutations)
      0
    (+
     (putnam-2023-b3-longest-zigzag-length
      (car permutations))
     (putnam-2023-b3-sum-longest-lengths
      (cdr permutations)))))

(defun putnam-2023-b3-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n
       (putnam-2023-b3-factorial (- n 1)))))

(defun putnam-2023-b3-expectation (n)
  (/
   (putnam-2023-b3-sum-longest-lengths
    (putnam-2023-b3-permutations
     (putnam-2023-b3-indices n)))
   (putnam-2023-b3-factorial n)))

(defun putnam-2023-b3-solution (n)
  (/ (+ (* 2 n) 2) 3))

(defun putnambench-putnam-2023-b3-statement (n)
  (implies
   (and (natp n)
        (<= 2 n))
   (equal
    (putnam-2023-b3-expectation n)
    (putnam-2023-b3-solution n))))

(value-triple :itpeval-statement-checked)
:q
