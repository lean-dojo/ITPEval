;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/isqrt_NewtonMethod_sqrtqtvc: the integer square-root Newton-method
;; verification condition, including initialization and universally quantified
;; loop preservation under truncated integer division. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Why3 mach.int.Int exports int.ComputerDivision, whose integer quotient is
;; truncated toward zero. The zero-divisor branch only totalizes this ACL2
;; helper; the verification condition supplies the corresponding nonzero
;; obligations wherever a division can affect the proposition.

(defun ntp4vc-isqrt-newton-tdiv (numerator denominator)
  (if (and
       (integerp numerator)
       (integerp denominator)
       (not (equal denominator 0)))
      (let ((quotient
             (floor
              (abs numerator)
              (abs denominator))))
        (if (or
             (and (< numerator 0) (< 0 denominator))
             (and (< 0 numerator) (< denominator 0)))
            (- quotient)
          quotient))
    0))

(defun ntp4vc-isqrt-newton-square (value)
  (* value value))

(defun ntp4vc-isqrt-newton-spec-p (x result)
  (and
   (<= 0 result)
   (<=
    (ntp4vc-isqrt-newton-square result)
    x)
   (<
    x
    (ntp4vc-isqrt-newton-square
     (+ result 1)))))

(defun ntp4vc-isqrt-newton-step (x y)
  (ntp4vc-isqrt-newton-tdiv
   (+
    (ntp4vc-isqrt-newton-tdiv x y)
    y)
   2))

(defun ntp4vc-isqrt-newton-loop-conclusion-p (x y)
  (let* ((step
          (ntp4vc-isqrt-newton-step x y))
         (next-step
          (ntp4vc-isqrt-newton-step x step)))
    (if (< step y)
        (and
         (not (equal step 0))
         (not (equal 2 0))
         (and
          (<= 0 y)
          (< step y))
         (< 0 next-step)
         (< 0 step)
         (<
          x
          (ntp4vc-isqrt-newton-square
           (+ step 1)))
         (<
          x
          (ntp4vc-isqrt-newton-square
           (+ next-step 1))))
      (ntp4vc-isqrt-newton-spec-p x y))))

(defun-sk ntp4vc-isqrt-newton-all-loop-states-p (x)
  (forall (y)
    (implies
     (integerp y)
     (let ((step
            (ntp4vc-isqrt-newton-step x y)))
       (implies
        (and
         (< 0 step)
         (< 0 y)
         (<
          x
          (ntp4vc-isqrt-newton-square
           (+ y 1)))
         (<
          x
          (ntp4vc-isqrt-newton-square
           (+ step 1))))
        (ntp4vc-isqrt-newton-loop-conclusion-p
         x y))))))

(defun ntp4vc-isqrt-newton-initialization-p (x)
  (let ((o1
         (ntp4vc-isqrt-newton-tdiv
          (+ 1 x)
          2)))
    (and
     (< 0 o1)
     (< 0 x)
     (equal
      o1
      (ntp4vc-isqrt-newton-step x x))
     (<
      x
      (ntp4vc-isqrt-newton-square
       (+ x 1)))
     (<
      x
      (ntp4vc-isqrt-newton-square
       (+ o1 1))))))

(defun ntp4vc-pearl-isqrt-newtonmethod-sqrtqtvc-statement (x)
  (implies
   (and
    (integerp x)
    (<= 0 x))
   (if (equal x 0)
       (ntp4vc-isqrt-newton-spec-p x 0)
     (if (<= x 3)
         (ntp4vc-isqrt-newton-spec-p x 1)
       (and
        (not (equal 2 0))
        (and
         (ntp4vc-isqrt-newton-initialization-p x)
         (ntp4vc-isqrt-newton-all-loop-states-p
          x)))))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
