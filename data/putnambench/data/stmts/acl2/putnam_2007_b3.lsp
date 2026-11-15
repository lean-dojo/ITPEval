;; Statement-only formalization of PutnamBench corpus artifact putnam_2007_b3:
;; the closed form for the 2007th term of the real recurrence
;; x_(n+1) = 3*x_n + floor(x_n*sqrt(5)), with x_0 = 1. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The source recurrence uniquely determines its real sequence. Starting at
;; 1, every term is a nonnegative integer; for such an integer m,
;;
;;   floor(m*sqrt(5)) = floor(sqrt(5*m^2)).
;;
;; Hence the internal integer recurrence below embeds into the source real
;; recurrence, and conversely every real sequence satisfying the source
;; initial value and recurrence agrees with it at every index by induction.
;; This gives a bidirectional equivalence rather than a restriction of the
;; source's real-valued sequence quantifier.
;;
;; The closed form lies in Q(sqrt(5)). A pair (a b) denotes a+b*sqrt(5), with
;; exact rational arithmetic. Pair addition, multiplication, and inversion
;; are the corresponding field operations, so equality with (x_2007 0) is
;; exactly the asserted real equality.

(defun putnam-2007-b3-isqrt-bisect
    (radicand lower upper fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (or (zp fuel)
          (<= upper (+ lower 1)))
      lower
    (let ((middle (floor (+ lower upper) 2)))
      (if (<= (* middle middle) radicand)
          (putnam-2007-b3-isqrt-bisect
           radicand middle upper (- fuel 1))
        (putnam-2007-b3-isqrt-bisect
         radicand lower middle (- fuel 1))))))

(defun putnam-2007-b3-isqrt (radicand)
  (let ((number (nfix radicand)))
    (putnam-2007-b3-isqrt-bisect
     number 0 (+ number 1) (+ number 1))))

(defun putnam-2007-b3-floor-times-sqrt-five (value)
  (putnam-2007-b3-isqrt
   (* 5 value value)))

(defun putnam-2007-b3-sequence (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (let ((previous
           (putnam-2007-b3-sequence (- n 1))))
      (+ (* 3 previous)
         (putnam-2007-b3-floor-times-sqrt-five
          previous)))))

(defun putnam-2007-b3-surd (rational-part root-part)
  (list rational-part root-part))

(defun putnam-2007-b3-surd-rational-part (value)
  (car value))

(defun putnam-2007-b3-surd-root-part (value)
  (cadr value))

(defun putnam-2007-b3-surd-add (left right)
  (putnam-2007-b3-surd
   (+ (putnam-2007-b3-surd-rational-part left)
      (putnam-2007-b3-surd-rational-part right))
   (+ (putnam-2007-b3-surd-root-part left)
      (putnam-2007-b3-surd-root-part right))))

(defun putnam-2007-b3-surd-multiply (left right)
  (let ((a (putnam-2007-b3-surd-rational-part left))
        (b (putnam-2007-b3-surd-root-part left))
        (c (putnam-2007-b3-surd-rational-part right))
        (d (putnam-2007-b3-surd-root-part right)))
    (putnam-2007-b3-surd
     (+ (* a c) (* 5 b d))
     (+ (* a d) (* b c)))))

(defun putnam-2007-b3-surd-inverse (value)
  (let* ((a
          (putnam-2007-b3-surd-rational-part value))
         (b
          (putnam-2007-b3-surd-root-part value))
         (norm
          (- (* a a) (* 5 b b))))
    (putnam-2007-b3-surd
     (/ a norm)
     (/ (- b) norm))))

(defun putnam-2007-b3-surd-power (base exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (putnam-2007-b3-surd 1 0)
    (putnam-2007-b3-surd-multiply
     base
     (putnam-2007-b3-surd-power
      base (- exponent 1)))))

(defun putnam-2007-b3-solution ()
  (let* ((one
          (putnam-2007-b3-surd 1 0))
         (two
          (putnam-2007-b3-surd 2 0))
         (sqrt-five
          (putnam-2007-b3-surd 0 1))
         (golden-ratio
          (putnam-2007-b3-surd-multiply
           (putnam-2007-b3-surd-add one sqrt-five)
           (putnam-2007-b3-surd-inverse two)))
         (golden-power
          (putnam-2007-b3-surd-power golden-ratio 4017))
         (two-power
          (putnam-2007-b3-surd-power two 2006)))
    (putnam-2007-b3-surd-multiply
     (putnam-2007-b3-surd-multiply
      two-power
      (putnam-2007-b3-surd-inverse sqrt-five))
     (putnam-2007-b3-surd-add
      golden-power
      (putnam-2007-b3-surd-inverse golden-power)))))

(defun putnambench-putnam-2007-b3-statement ()
  (equal
   (putnam-2007-b3-surd
    (putnam-2007-b3-sequence 2007)
    0)
   (putnam-2007-b3-solution)))

(value-triple :itpeval-statement-checked)
:q
