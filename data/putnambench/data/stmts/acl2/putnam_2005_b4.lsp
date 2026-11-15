;; Statement-only formalization of PutnamBench corpus artifact putnam_2005_b4:
;; for positive integers m and n, the number of integer n-tuples whose sum of
;; absolute values is at most m is unchanged when m and n are exchanged. This
;; file contains no proof.

(in-package "ACL2")

;; For fixed M, a base-(2M+1) digit D represents the integer D-M. Codes below
;; (2M+1)^N therefore represent all integer N-tuples in [-M,M]^N bijectively.

(defun putnam-2005-b4-coordinate (code index m)
  (let* ((base (+ (* 2 (nfix m)) 1))
         (digit (mod (floor (nfix code) (expt base (nfix index)))
                     base)))
    (- digit (nfix m))))

(defun putnam-2005-b4-absolute-sum (code coordinate-count m)
  (declare (xargs :measure (nfix coordinate-count)))
  (if (zp coordinate-count)
      0
    (let ((index (- coordinate-count 1)))
      (+ (abs (putnam-2005-b4-coordinate code index m))
         (putnam-2005-b4-absolute-sum code index m)))))

(defun putnam-2005-b4-count-codes (candidate-count n m)
  (declare (xargs :measure (nfix candidate-count)))
  (if (zp candidate-count)
      0
    (let ((code (- candidate-count 1)))
      (+ (if (<= (putnam-2005-b4-absolute-sum code n m)
                 (nfix m))
             1
           0)
         (putnam-2005-b4-count-codes code n m)))))

(defun putnam-2005-b4-tuple-count (m n)
  (let* ((fixed-m (nfix m))
         (fixed-n (nfix n))
         (base (+ (* 2 fixed-m) 1)))
    (putnam-2005-b4-count-codes
     (expt base fixed-n)
     fixed-n
     fixed-m)))

(defun putnambench-putnam-2005-b4-statement (m n)
  (implies
   (and (natp m)
        (< 0 m)
        (natp n)
        (< 0 n))
   (equal (putnam-2005-b4-tuple-count m n)
          (putnam-2005-b4-tuple-count n m))))

(value-triple :itpeval-statement-checked)
:q
