;; Statement-only formalization of PutnamBench corpus artifact putnam_1980_a4:
;; bounded nonzero integer combinations of 1, sqrt(2), and sqrt(3) include
;; one with absolute value below 10^-11, while all have absolute value above
;; 10^-21. This file contains no proof.

(in-package "ACL2")

;; Exact positivity for p + q*sqrt(2), using rational comparisons only.
(defun putnam-1980-a4-qsqrt2-positive-p (p q)
  (and
   (rationalp p)
   (rationalp q)
   (cond
    ((equal q 0)
     (< 0 p))
    ((< 0 q)
     (or (<= 0 p)
         (< (* p p) (* 2 q q))))
    (t
     (and (< 0 p)
          (< (* 2 q q) (* p p)))))))

;; Exact positivity for d + b*sqrt(2) + c*sqrt(3). If the first two
;; terms and c*sqrt(3) have opposite signs, squaring reduces the comparison
;; to one in Q(sqrt(2)); the sign checks make every squaring step reversible.
(defun putnam-1980-a4-qsqrt2-sqrt3-positive-p (d b c)
  (and
   (rationalp d)
   (rationalp b)
   (rationalp c)
   (let ((u-positive
          (putnam-1980-a4-qsqrt2-positive-p d b))
         (u-zero
          (and (equal d 0)
               (equal b 0))))
     (cond
      ((equal c 0)
       u-positive)
      ((< 0 c)
       (or
        u-positive
        u-zero
        (putnam-1980-a4-qsqrt2-positive-p
         (- (* 3 c c)
            (+ (* d d) (* 2 b b)))
         (- (* 2 d b)))))
      (t
       (and
        u-positive
        (putnam-1980-a4-qsqrt2-positive-p
         (- (+ (* d d) (* 2 b b))
            (* 3 c c))
         (* 2 d b))))))))

(defun putnam-1980-a4-abcvals-p (a b c)
  (and
   (integerp a)
   (integerp b)
   (integerp c)
   (not (and (equal a 0)
             (equal b 0)
             (equal c 0)))
   (< (abs a) 1000000)
   (< (abs b) 1000000)
   (< (abs c) 1000000)))

(defun putnam-1980-a4-absolute-less-p (a b c epsilon)
  (and
   (rationalp epsilon)
   (< 0 epsilon)
   (putnam-1980-a4-qsqrt2-sqrt3-positive-p
    (+ a epsilon) b c)
   (putnam-1980-a4-qsqrt2-sqrt3-positive-p
    (- epsilon a) (- b) (- c))))

(defun putnam-1980-a4-absolute-greater-p (a b c epsilon)
  (and
   (rationalp epsilon)
   (< 0 epsilon)
   (or
    (putnam-1980-a4-qsqrt2-sqrt3-positive-p
     (- a epsilon) b c)
    (putnam-1980-a4-qsqrt2-sqrt3-positive-p
     (- (- a) epsilon) (- b) (- c)))))

;; The source restrictions make each quantified integer range exactly
;; {-999999,...,999999}. These searches implement the internal existential
;; quantifiers without exposing their witnesses as statement parameters.
(defun putnam-1980-a4-small-c-exists-p (a b c-index)
  (declare (xargs :measure (nfix c-index)))
  (if (and (integerp a)
           (integerp b)
           (natp c-index))
      (let ((c (- c-index 999999)))
        (or
         (and
          (putnam-1980-a4-abcvals-p a b c)
          (putnam-1980-a4-absolute-less-p
           a b c (/ 1 (expt 10 11))))
         (and
          (not (zp c-index))
          (putnam-1980-a4-small-c-exists-p
           a b (- c-index 1)))))
    nil))

(defun putnam-1980-a4-small-bc-exists-p (a b-index)
  (declare (xargs :measure (nfix b-index)))
  (if (and (integerp a)
           (natp b-index))
      (let ((b (- b-index 999999)))
        (or
         (putnam-1980-a4-small-c-exists-p
          a b 1999998)
         (and
          (not (zp b-index))
          (putnam-1980-a4-small-bc-exists-p
           a (- b-index 1)))))
    nil))

(defun putnam-1980-a4-small-abc-exists-p (a-index)
  (declare (xargs :measure (nfix a-index)))
  (if (natp a-index)
      (let ((a (- a-index 999999)))
        (or
         (putnam-1980-a4-small-bc-exists-p
          a 1999998)
         (and
          (not (zp a-index))
          (putnam-1980-a4-small-abc-exists-p
           (- a-index 1)))))
    nil))

;; Recursion over the same complete ranges implements the source universal
;; quantifiers. Outside these ranges ABCVALS is false in the source.
(defun putnam-1980-a4-large-for-every-c-p (a b c-index)
  (declare (xargs :measure (nfix c-index)))
  (if (and (integerp a)
           (integerp b)
           (natp c-index))
      (let ((c (- c-index 999999)))
        (and
         (implies
          (putnam-1980-a4-abcvals-p a b c)
          (putnam-1980-a4-absolute-greater-p
           a b c (/ 1 (expt 10 21))))
         (or
          (zp c-index)
          (putnam-1980-a4-large-for-every-c-p
           a b (- c-index 1)))))
    nil))

(defun putnam-1980-a4-large-for-every-bc-p (a b-index)
  (declare (xargs :measure (nfix b-index)))
  (if (and (integerp a)
           (natp b-index))
      (let ((b (- b-index 999999)))
        (and
         (putnam-1980-a4-large-for-every-c-p
          a b 1999998)
         (or
          (zp b-index)
          (putnam-1980-a4-large-for-every-bc-p
           a (- b-index 1)))))
    nil))

(defun putnam-1980-a4-large-for-every-abc-p (a-index)
  (declare (xargs :measure (nfix a-index)))
  (if (natp a-index)
      (let ((a (- a-index 999999)))
        (and
         (putnam-1980-a4-large-for-every-bc-p
          a 1999998)
         (or
          (zp a-index)
          (putnam-1980-a4-large-for-every-abc-p
           (- a-index 1)))))
    nil))

(defun putnambench-putnam-1980-a4-statement ()
  (and
   (putnam-1980-a4-small-abc-exists-p 1999998)
   (putnam-1980-a4-large-for-every-abc-p 1999998)))

(value-triple :itpeval-statement-checked)
:q
