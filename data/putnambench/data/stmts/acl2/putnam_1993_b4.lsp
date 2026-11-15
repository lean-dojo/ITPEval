;; Statement-only formalization of PutnamBench corpus artifact putnam_1993_b4:
;; positive continuous real functions coupled by a positive continuous kernel
;; on the unit interval through two integral equations are equal there. This
;; file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; FUNCTION(x,epsilon) and KERNEL(x,y,epsilon) are rational regular Cauchy
;; names for exact real values at rational points of [0,1]. Internal moduli
;; give their unique continuous extensions to the compact interval and square.
;; Since only these restrictions occur in the source proposition, this is
;; equivalent to its total real-function presentation.
;;
;; Strict positivity on a compact domain is equivalently expressed by an
;; internally existential uniform positive rational lower bound. The integral
;; equations use the double limit of rational right Riemann sums as the mesh
;; and value precision tend to zero. For the continuous source integrands this
;; limit is exactly the stated Lebesgue interval integral. Equality on the
;; dense rational points then extends to every real point of [0,1].

(defun p93b4-abs (x)
  (if (< x 0) (- x) x))

(defun p93b4-positive-rational-p (x)
  (and (rationalp x) (< 0 x)))

(defun p93b4-unit-rational-p (x)
  (and (rationalp x) (<= 0 x) (<= x 1)))

(defun p93b4-function-value (function x precision)
  (apply$ function (list x precision)))

(defun p93b4-kernel-value (kernel x y precision)
  (apply$ kernel (list x y precision)))

(defun-sk p93b4-function-name-p (function)
  (forall (x epsilon eta)
    (implies
     (and
      (p93b4-unit-rational-p x)
      (p93b4-positive-rational-p epsilon)
      (p93b4-positive-rational-p eta))
     (and
      (rationalp
       (p93b4-function-value function x epsilon))
      (rationalp
       (p93b4-function-value function x eta))
      (<=
       (p93b4-abs
        (-
         (p93b4-function-value function x epsilon)
         (p93b4-function-value function x eta)))
       (+ epsilon eta))))))

(defun-sk p93b4-kernel-name-p (kernel)
  (forall (x y epsilon eta)
    (implies
     (and
      (p93b4-unit-rational-p x)
      (p93b4-unit-rational-p y)
      (p93b4-positive-rational-p epsilon)
      (p93b4-positive-rational-p eta))
     (and
      (rationalp
       (p93b4-kernel-value kernel x y epsilon))
      (rationalp
       (p93b4-kernel-value kernel x y eta))
      (<=
       (p93b4-abs
        (-
         (p93b4-kernel-value kernel x y epsilon)
         (p93b4-kernel-value kernel x y eta)))
       (+ epsilon eta))))))

(defun-sk p93b4-function-modulus-p (function modulus)
  (forall (x y epsilon)
    (implies
     (and
      (p93b4-unit-rational-p x)
      (p93b4-unit-rational-p y)
      (p93b4-positive-rational-p epsilon))
     (let ((delta (apply$ modulus (list epsilon))))
       (and
        (p93b4-positive-rational-p delta)
        (implies
         (< (p93b4-abs (- x y)) delta)
         (<=
          (p93b4-abs
           (-
            (p93b4-function-value
             function x (/ epsilon 4))
            (p93b4-function-value
             function y (/ epsilon 4))))
          epsilon)))))))

(defun-sk p93b4-function-continuous-p (function)
  (exists (modulus)
    (and
     (tamep-functionp modulus)
     (p93b4-function-modulus-p function modulus))))

(defun-sk p93b4-kernel-modulus-p (kernel modulus)
  (forall (x1 y1 x2 y2 epsilon)
    (implies
     (and
      (p93b4-unit-rational-p x1)
      (p93b4-unit-rational-p y1)
      (p93b4-unit-rational-p x2)
      (p93b4-unit-rational-p y2)
      (p93b4-positive-rational-p epsilon))
     (let ((delta (apply$ modulus (list epsilon))))
       (and
        (p93b4-positive-rational-p delta)
        (implies
         (<
          (+
           (p93b4-abs (- x1 x2))
           (p93b4-abs (- y1 y2)))
          delta)
         (<=
          (p93b4-abs
           (-
            (p93b4-kernel-value
             kernel x1 y1 (/ epsilon 4))
            (p93b4-kernel-value
             kernel x2 y2 (/ epsilon 4))))
          epsilon)))))))

(defun-sk p93b4-kernel-continuous-p (kernel)
  (exists (modulus)
    (and
     (tamep-functionp modulus)
     (p93b4-kernel-modulus-p kernel modulus))))

(defun-sk p93b4-function-positive-bound-p
    (function lower)
  (forall (x epsilon)
    (implies
     (and
      (p93b4-unit-rational-p x)
      (p93b4-positive-rational-p epsilon))
     (<=
      lower
      (+ (p93b4-function-value function x epsilon)
         epsilon)))))

(defun-sk p93b4-function-positive-p (function)
  (exists (lower)
    (and
     (p93b4-positive-rational-p lower)
     (p93b4-function-positive-bound-p
      function lower))))

(defun-sk p93b4-kernel-positive-bound-p
    (kernel lower)
  (forall (x y epsilon)
    (implies
     (and
      (p93b4-unit-rational-p x)
      (p93b4-unit-rational-p y)
      (p93b4-positive-rational-p epsilon))
     (<=
      lower
      (+ (p93b4-kernel-value
          kernel x y epsilon)
         epsilon)))))

(defun-sk p93b4-kernel-positive-p (kernel)
  (exists (lower)
    (and
     (p93b4-positive-rational-p lower)
     (p93b4-kernel-positive-bound-p
      kernel lower))))

(defun p93b4-riemann-numerator
    (index pieces x precision function kernel)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      0
    (let ((y (/ index pieces)))
      (+
       (*
        (p93b4-function-value function y precision)
        (p93b4-kernel-value kernel x y precision))
       (p93b4-riemann-numerator
        (- index 1)
        pieces
        x
        precision
        function
        kernel)))))

(defun p93b4-riemann-sum
    (pieces x precision function kernel)
  (if (posp pieces)
      (/
       (p93b4-riemann-numerator
        pieces pieces x precision function kernel)
       pieces)
    0))

(defun-sk p93b4-integral-tail-p
    (function kernel result x epsilon cutoff precision-cutoff)
  (forall (pieces precision)
    (implies
     (and
      (posp pieces)
      (posp cutoff)
      (<= cutoff pieces)
      (p93b4-positive-rational-p precision)
      (p93b4-positive-rational-p precision-cutoff)
      (<= precision precision-cutoff))
     (<=
      (p93b4-abs
       (-
        (p93b4-riemann-sum
         pieces x precision function kernel)
        (p93b4-function-value result x precision)))
      epsilon))))

(defun-sk p93b4-integral-tail-exists-p
    (function kernel result x epsilon)
  (exists (cutoff precision-cutoff)
    (and
     (posp cutoff)
     (p93b4-positive-rational-p precision-cutoff)
     (p93b4-integral-tail-p
      function kernel result x epsilon
      cutoff precision-cutoff))))

(defun-sk p93b4-integral-equation-at-p
    (function kernel result x)
  (forall (epsilon)
    (implies
     (p93b4-positive-rational-p epsilon)
     (p93b4-integral-tail-exists-p
      function kernel result x epsilon))))

(defun-sk p93b4-integral-equations-p
    (kernel f g)
  (forall (x)
    (implies
     (p93b4-unit-rational-p x)
     (and
      (p93b4-integral-equation-at-p f kernel g x)
      (p93b4-integral-equation-at-p g kernel f x)))))

(defun-sk p93b4-equal-on-unit-p (f g)
  (forall (x epsilon)
    (implies
     (and
      (p93b4-unit-rational-p x)
      (p93b4-positive-rational-p epsilon))
     (<=
      (p93b4-abs
       (-
        (p93b4-function-value f x epsilon)
        (p93b4-function-value g x epsilon)))
      (* 2 epsilon)))))

(defun putnambench-putnam-1993-b4-statement
    (kernel f g)
  (implies
   (and
    (tamep-functionp kernel)
    (tamep-functionp f)
    (tamep-functionp g)
    (p93b4-kernel-name-p kernel)
    (p93b4-function-name-p f)
    (p93b4-function-name-p g)
    (p93b4-kernel-continuous-p kernel)
    (p93b4-function-continuous-p f)
    (p93b4-function-continuous-p g)
    (p93b4-kernel-positive-p kernel)
    (p93b4-function-positive-p f)
    (p93b4-function-positive-p g)
    (p93b4-integral-equations-p kernel f g))
   (p93b4-equal-on-unit-p f g)))

(value-triple :itpeval-statement-checked)
:q
