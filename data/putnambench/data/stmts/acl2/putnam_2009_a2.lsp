;; Statement-only formalization of PutnamBench corpus artifact putnam_2009_a2:
;; the local real solution of the stated three-function differential system
;; has the given trigonometric real-power formula. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Near zero all three source functions remain nonzero, so the analytic
;; right-hand side of the ODE makes every differentiable source solution
;; analytic. Its Taylor coefficients are therefore uniquely forced by the
;; three recurrences below.
;;
;; Writing s = sin(6x) and c = cos(6x), the displayed source formula
;;
;;   2^(-1/12) * (sin(6x+pi/4) / cos(6x+pi/4)^2)^(1/6)
;;
;; is, on a neighborhood of zero, the unique positive analytic germ F with
;; F(0)=1 and F^6*(c-s)^2=s+c. Thus the source conclusion is equivalent in
;; both directions to equality of every Taylor coefficient in the final
;; predicate. All coefficients are rational, but this is an exact analytic
;; germ encoding, not a restriction of the source real domain.

(defun putnam-2009-a2-factorial (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      1
    (* n (putnam-2009-a2-factorial (- n 1)))))

(defun putnam-2009-a2-sine-coefficient (degree)
  (if (and (natp degree) (oddp degree))
      (/ (* (expt -1 (floor degree 2))
            (expt 6 degree))
         (putnam-2009-a2-factorial degree))
    0))

(defun putnam-2009-a2-cosine-coefficient (degree)
  (if (and (natp degree) (evenp degree))
      (/ (* (expt -1 (floor degree 2))
            (expt 6 degree))
         (putnam-2009-a2-factorial degree))
    0))

(defun putnam-2009-a2-series-coefficient (series degree)
  (if (and (natp degree)
           (< degree (len series)))
      (nth degree series)
    0))

(defun putnam-2009-a2-convolution-coefficient-aux
    (left right degree remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (let ((index (- (+ degree 1) remaining)))
      (+ (* (putnam-2009-a2-series-coefficient left index)
            (putnam-2009-a2-series-coefficient
             right (- degree index)))
         (putnam-2009-a2-convolution-coefficient-aux
          left right degree (- remaining 1))))))

(defun putnam-2009-a2-convolution-coefficient
    (left right degree)
  (if (natp degree)
      (putnam-2009-a2-convolution-coefficient-aux
       left right degree (+ degree 1))
    0))

(defun putnam-2009-a2-series-product-prefix-aux
    (left right index remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (cons
     (putnam-2009-a2-convolution-coefficient
      left right index)
     (putnam-2009-a2-series-product-prefix-aux
      left right (+ index 1) (- remaining 1)))))

(defun putnam-2009-a2-series-product-prefix
    (left right count)
  (putnam-2009-a2-series-product-prefix-aux
   left right 0 count))

(defun putnam-2009-a2-zero-prefix (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons 0 (putnam-2009-a2-zero-prefix (- count 1)))))

(defun putnam-2009-a2-one-prefix (count)
  (if (zp count)
      nil
    (cons 1 (putnam-2009-a2-zero-prefix (- count 1)))))

(defun putnam-2009-a2-series-power-prefix
    (series power count)
  (declare (xargs :measure (nfix power)))
  (if (zp power)
      (putnam-2009-a2-one-prefix count)
    (putnam-2009-a2-series-product-prefix
     series
     (putnam-2009-a2-series-power-prefix
      series (- power 1) count)
     count)))

(defun putnam-2009-a2-series-difference-prefix-aux
    (left right index remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (cons
     (- (putnam-2009-a2-series-coefficient left index)
        (putnam-2009-a2-series-coefficient right index))
     (putnam-2009-a2-series-difference-prefix-aux
      left right (+ index 1) (- remaining 1)))))

(defun putnam-2009-a2-series-difference-prefix
    (left right count)
  (putnam-2009-a2-series-difference-prefix-aux
   left right 0 count))

(defun putnam-2009-a2-sine-prefix-aux (index remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (cons
     (putnam-2009-a2-sine-coefficient index)
     (putnam-2009-a2-sine-prefix-aux
      (+ index 1) (- remaining 1)))))

(defun putnam-2009-a2-sine-prefix (count)
  (putnam-2009-a2-sine-prefix-aux 0 count))

(defun putnam-2009-a2-cosine-prefix-aux (index remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (cons
     (putnam-2009-a2-cosine-coefficient index)
     (putnam-2009-a2-cosine-prefix-aux
      (+ index 1) (- remaining 1)))))

(defun putnam-2009-a2-cosine-prefix (count)
  (putnam-2009-a2-cosine-prefix-aux 0 count))

(defun putnam-2009-a2-reciprocal-sum-aux
    (series reciprocal degree remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (let ((index (+ 1 (- degree remaining))))
      (+ (* (putnam-2009-a2-series-coefficient series index)
            (putnam-2009-a2-series-coefficient
             reciprocal (- degree index)))
         (putnam-2009-a2-reciprocal-sum-aux
          series reciprocal degree (- remaining 1))))))

(defun putnam-2009-a2-reciprocal-next-coefficient
    (series reciprocal degree)
  (if (zp degree)
      (/ (putnam-2009-a2-series-coefficient series 0))
    (- (/ (putnam-2009-a2-reciprocal-sum-aux
           series reciprocal degree degree)
          (putnam-2009-a2-series-coefficient series 0)))))

(defun putnam-2009-a2-reciprocal-prefix-aux
    (series reciprocal index remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      reciprocal
    (putnam-2009-a2-reciprocal-prefix-aux
     series
     (append
      reciprocal
      (list
       (putnam-2009-a2-reciprocal-next-coefficient
        series reciprocal index)))
     (+ index 1)
     (- remaining 1))))

(defun putnam-2009-a2-reciprocal-prefix (series count)
  (putnam-2009-a2-reciprocal-prefix-aux
   series nil 0 count))

(defun putnam-2009-a2-f-rhs-coefficient
    (f g h degree)
  (let* ((count (+ degree 1))
         (f-squared
          (putnam-2009-a2-series-power-prefix f 2 count))
         (f-squared-g
          (putnam-2009-a2-series-product-prefix
           f-squared g count))
         (f-squared-g-h
          (putnam-2009-a2-series-product-prefix
           f-squared-g h count))
         (g-h
          (putnam-2009-a2-series-product-prefix g h count))
         (inverse-g-h
          (putnam-2009-a2-reciprocal-prefix g-h count)))
    (+ (* 2
          (putnam-2009-a2-series-coefficient
           f-squared-g-h degree))
       (putnam-2009-a2-series-coefficient
        inverse-g-h degree))))

(defun putnam-2009-a2-g-rhs-coefficient
    (f g h degree)
  (let* ((count (+ degree 1))
         (g-squared
          (putnam-2009-a2-series-power-prefix g 2 count))
         (f-g-squared
          (putnam-2009-a2-series-product-prefix
           f g-squared count))
         (f-g-squared-h
          (putnam-2009-a2-series-product-prefix
           f-g-squared h count))
         (f-h
          (putnam-2009-a2-series-product-prefix f h count))
         (inverse-f-h
          (putnam-2009-a2-reciprocal-prefix f-h count)))
    (+ (putnam-2009-a2-series-coefficient
        f-g-squared-h degree)
       (* 4
          (putnam-2009-a2-series-coefficient
           inverse-f-h degree)))))

(defun putnam-2009-a2-h-rhs-coefficient
    (f g h degree)
  (let* ((count (+ degree 1))
         (h-squared
          (putnam-2009-a2-series-power-prefix h 2 count))
         (f-g
          (putnam-2009-a2-series-product-prefix f g count))
         (f-g-h-squared
          (putnam-2009-a2-series-product-prefix
           f-g h-squared count))
         (inverse-f-g
          (putnam-2009-a2-reciprocal-prefix f-g count)))
    (+ (* 3
          (putnam-2009-a2-series-coefficient
           f-g-h-squared degree))
       (putnam-2009-a2-series-coefficient
        inverse-f-g degree))))

(defun putnam-2009-a2-solution-prefix-aux (remaining coefficient-triple)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      coefficient-triple
    (let* ((f (car coefficient-triple))
           (g (cadr coefficient-triple))
           (h (caddr coefficient-triple))
           (degree (- (len f) 1))
           (divisor (+ degree 1))
           (next-f
            (/ (putnam-2009-a2-f-rhs-coefficient
                f g h degree)
               divisor))
           (next-g
            (/ (putnam-2009-a2-g-rhs-coefficient
                f g h degree)
               divisor))
           (next-h
            (/ (putnam-2009-a2-h-rhs-coefficient
                f g h degree)
               divisor)))
      (putnam-2009-a2-solution-prefix-aux
       (- remaining 1)
       (list
        (append f (list next-f))
        (append g (list next-g))
        (append h (list next-h)))))))

(defun putnam-2009-a2-solution-prefix (degree)
  (if (natp degree)
      (putnam-2009-a2-solution-prefix-aux
       degree (list (list 1) (list 1) (list 1)))
    (list (list 1) (list 1) (list 1))))

(defun putnambench-putnam-2009-a2-statement (degree)
  (implies
   (natp degree)
   (let* ((count (+ degree 1))
          (solution
           (putnam-2009-a2-solution-prefix degree))
          (f (car solution))
          (sine (putnam-2009-a2-sine-prefix count))
          (cosine (putnam-2009-a2-cosine-prefix count))
          (cosine-minus-sine
           (putnam-2009-a2-series-difference-prefix
            cosine sine count))
          (f-sixth
           (putnam-2009-a2-series-power-prefix f 6 count))
          (cosine-minus-sine-squared
           (putnam-2009-a2-series-power-prefix
            cosine-minus-sine 2 count))
          (left
           (putnam-2009-a2-series-product-prefix
            f-sixth cosine-minus-sine-squared count)))
     (equal
      (putnam-2009-a2-series-coefficient left degree)
      (+ (putnam-2009-a2-sine-coefficient degree)
         (putnam-2009-a2-cosine-coefficient degree))))))

(value-triple :itpeval-statement-checked)
:q
