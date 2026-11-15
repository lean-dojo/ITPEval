;; Statement-only formalization of hundred-theorems corpus artifact 015,
;; "The Fundamental Theorem of Integral Calculus": on a closed real interval,
;; an interval-relative derivative integrates to the difference of endpoint
;; values. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Real values, real functions, gauges, and sets are arbitrary ACL2 objects
;; interpreted by fixed-arity conservative interfaces. Mathematical
;; quantifiers are formula-specific DEFUN-SK binders; no finite function
;; table or generic function evaluator is used.

(defstub ftc15-real-p (r-type value) t)
(defstub ftc15-zero (r-type) t)
(defstub ftc15-one (r-type) t)
(defstub ftc15-add (r-type left right) t)
(defstub ftc15-mul (r-type left right) t)
(defstub ftc15-neg (r-type value) t)
(defstub ftc15-inv (r-type value) t)
(defstub ftc15-lt (r-type left right) t)

(defstub ftc15-function-value (r-type function argument) t)
(defstub ftc15-set-member-p (r-type set value) t)

(defun ftc15-sub (r-type x y)
  (ftc15-add r-type x (ftc15-neg r-type y)))

(defun ftc15-le (r-type x y)
  (not (ftc15-lt r-type y x)))

(defun ftc15-abs (r-type x)
  (if (ftc15-lt r-type x (ftc15-zero r-type))
      (ftc15-neg r-type x)
    x))

(defun ftc15-in-closed-interval-p (r-type a b x)
  (and (ftc15-real-p r-type x)
       (ftc15-le r-type a x)
       (ftc15-le r-type x b)))

;; A complete ordered-field presentation of the real carrier.

(defun-sk ftc15-operation-closure-p (r-type)
  (forall (x y)
    (and
     (ftc15-real-p r-type (ftc15-zero r-type))
     (ftc15-real-p r-type (ftc15-one r-type))
     (implies
      (ftc15-real-p r-type x)
      (and
       (ftc15-real-p r-type (ftc15-neg r-type x))
       (ftc15-real-p r-type (ftc15-inv r-type x))))
     (implies
      (and (ftc15-real-p r-type x)
           (ftc15-real-p r-type y))
      (and
       (ftc15-real-p r-type (ftc15-add r-type x y))
       (ftc15-real-p r-type (ftc15-mul r-type x y)))))))

(defun-sk ftc15-unary-field-laws-p (r-type)
  (forall (x)
    (implies
     (ftc15-real-p r-type x)
     (let ((zero (ftc15-zero r-type))
           (one (ftc15-one r-type)))
       (and
        (equal (ftc15-add r-type zero x) x)
        (equal (ftc15-add r-type x zero) x)
        (equal (ftc15-add r-type x (ftc15-neg r-type x)) zero)
        (equal (ftc15-add r-type (ftc15-neg r-type x) x) zero)
        (equal (ftc15-mul r-type one x) x)
        (equal (ftc15-mul r-type x one) x)
        (implies
         (not (equal x zero))
         (and
          (equal (ftc15-mul r-type x (ftc15-inv r-type x)) one)
          (equal (ftc15-mul r-type (ftc15-inv r-type x) x) one))))))))

(defun-sk ftc15-binary-field-laws-p (r-type)
  (forall (x y)
    (implies
     (and (ftc15-real-p r-type x)
          (ftc15-real-p r-type y))
     (and
      (equal (ftc15-add r-type x y)
             (ftc15-add r-type y x))
      (equal (ftc15-mul r-type x y)
             (ftc15-mul r-type y x))))))

(defun-sk ftc15-ternary-field-laws-p (r-type)
  (forall (x y z)
    (implies
     (and (ftc15-real-p r-type x)
          (ftc15-real-p r-type y)
          (ftc15-real-p r-type z))
     (and
      (equal
       (ftc15-add r-type (ftc15-add r-type x y) z)
       (ftc15-add r-type x (ftc15-add r-type y z)))
      (equal
       (ftc15-mul r-type (ftc15-mul r-type x y) z)
       (ftc15-mul r-type x (ftc15-mul r-type y z)))
      (equal
       (ftc15-mul r-type x (ftc15-add r-type y z))
       (ftc15-add r-type
                  (ftc15-mul r-type x y)
                  (ftc15-mul r-type x z)))))))

(defun-sk ftc15-order-laws-p (r-type)
  (forall (x y z)
    (implies
     (and (ftc15-real-p r-type x)
          (ftc15-real-p r-type y)
          (ftc15-real-p r-type z))
     (and
      (not (ftc15-lt r-type x x))
      (implies
       (and (ftc15-lt r-type x y)
            (ftc15-lt r-type y z))
       (ftc15-lt r-type x z))
      (or (ftc15-lt r-type x y)
          (equal x y)
          (ftc15-lt r-type y x))
      (implies
       (ftc15-lt r-type x y)
       (ftc15-lt r-type
                 (ftc15-add r-type x z)
                 (ftc15-add r-type y z)))
      (implies
       (and (ftc15-lt r-type (ftc15-zero r-type) x)
            (ftc15-lt r-type (ftc15-zero r-type) y))
       (ftc15-lt r-type
                 (ftc15-zero r-type)
                 (ftc15-mul r-type x y)))))))

(defun-sk ftc15-valid-real-set-p (r-type set)
  (forall (x)
    (implies
     (ftc15-set-member-p r-type set x)
     (ftc15-real-p r-type x))))

(defun-sk ftc15-set-nonempty-p (r-type set)
  (exists (x)
    (and (ftc15-real-p r-type x)
         (ftc15-set-member-p r-type set x))))

(defun-sk ftc15-upper-bound-p (r-type set bound)
  (forall (x)
    (implies
     (ftc15-set-member-p r-type set x)
     (ftc15-le r-type x bound))))

(defun-sk ftc15-set-bounded-above-p (r-type set)
  (exists (bound)
    (and (ftc15-real-p r-type bound)
         (ftc15-upper-bound-p r-type set bound))))

(defun-sk ftc15-least-upper-bound-p (r-type set supremum)
  (forall (bound)
    (and
     (ftc15-real-p r-type supremum)
     (ftc15-upper-bound-p r-type set supremum)
     (implies
      (and (ftc15-real-p r-type bound)
           (ftc15-upper-bound-p r-type set bound))
      (ftc15-le r-type supremum bound)))))

(defun-sk ftc15-supremum-exists-p (r-type set)
  (exists (supremum)
    (and (ftc15-real-p r-type supremum)
         (ftc15-least-upper-bound-p r-type set supremum))))

(defun-sk ftc15-dedekind-complete-p (r-type)
  (forall (set)
    (implies
     (and (ftc15-valid-real-set-p r-type set)
          (ftc15-set-nonempty-p r-type set)
          (ftc15-set-bounded-above-p r-type set))
     (ftc15-supremum-exists-p r-type set))))

(defun ftc15-real-structure-p (r-type)
  (and
   (ftc15-operation-closure-p r-type)
   (ftc15-unary-field-laws-p r-type)
   (ftc15-binary-field-laws-p r-type)
   (ftc15-ternary-field-laws-p r-type)
   (ftc15-order-laws-p r-type)
   (not (equal (ftc15-zero r-type) (ftc15-one r-type)))
   (ftc15-lt r-type (ftc15-zero r-type) (ftc15-one r-type))
   (ftc15-dedekind-complete-p r-type)))

;; Arbitrary real-valued functions are total on the real carrier.

(defun-sk ftc15-real-function-p (r-type function)
  (forall (x)
    (implies
     (ftc15-real-p r-type x)
     (ftc15-real-p
      r-type
      (ftc15-function-value r-type function x)))))

;; The derivative is relative to [a,b], matching the one-sided endpoint
;; interpretation in the source statements. The residual formulation
;; |f(y)-f(x)-d(y-x)| <= epsilon |y-x| also covers y = x directly.

(defun-sk ftc15-derivative-neighborhood-p
    (r-type function derivative a b x epsilon radius)
  (forall (y)
    (implies
     (and
      (ftc15-in-closed-interval-p r-type a b y)
      (ftc15-lt
       r-type
       (ftc15-abs r-type (ftc15-sub r-type y x))
       radius))
     (ftc15-le
      r-type
      (ftc15-abs
       r-type
       (ftc15-sub
        r-type
        (ftc15-sub
         r-type
         (ftc15-function-value r-type function y)
         (ftc15-function-value r-type function x))
        (ftc15-mul
         r-type
         derivative
         (ftc15-sub r-type y x))))
      (ftc15-mul
       r-type
       epsilon
       (ftc15-abs r-type (ftc15-sub r-type y x)))))))

(defun-sk ftc15-derivative-radius-exists-p
    (r-type function derivative a b x epsilon)
  (exists (radius)
    (and
     (ftc15-real-p r-type radius)
     (ftc15-lt r-type (ftc15-zero r-type) radius)
     (ftc15-derivative-neighborhood-p
      r-type function derivative a b x epsilon radius))))

(defun-sk ftc15-has-derivative-within-p
    (r-type function derivative a b x)
  (forall (epsilon)
    (implies
     (and
      (ftc15-real-p r-type epsilon)
      (ftc15-lt r-type (ftc15-zero r-type) epsilon))
     (ftc15-derivative-radius-exists-p
      r-type function derivative a b x epsilon))))

(defun-sk ftc15-derivative-on-closed-interval-p
    (r-type function derivative-function a b)
  (forall (x)
    (implies
     (ftc15-in-closed-interval-p r-type a b x)
     (ftc15-has-derivative-within-p
      r-type
      function
      (ftc15-function-value r-type derivative-function x)
      a b x))))

;; A tagged division is an intrinsically finite list of triples
;; (tag left-endpoint right-endpoint), ordered from a to b.

(defun ftc15-tagged-piece-p (r-type piece)
  (and
   (true-listp piece)
   (equal (len piece) 3)
   (ftc15-real-p r-type (nth 0 piece))
   (ftc15-real-p r-type (nth 1 piece))
   (ftc15-real-p r-type (nth 2 piece))
   (ftc15-lt r-type (nth 1 piece) (nth 2 piece))
   (ftc15-le r-type (nth 1 piece) (nth 0 piece))
   (ftc15-le r-type (nth 0 piece) (nth 2 piece))))

(defun ftc15-tagged-division-tail-p (r-type division next-left b)
  (if (endp division)
      (equal next-left b)
    (let ((piece (car division)))
      (and
       (ftc15-tagged-piece-p r-type piece)
       (equal (nth 1 piece) next-left)
       (ftc15-tagged-division-tail-p
        r-type
        (cdr division)
        (nth 2 piece)
        b)))))

(defun ftc15-tagged-division-p (r-type a b division)
  (and
   (true-listp division)
   (ftc15-real-p r-type a)
   (ftc15-real-p r-type b)
   (ftc15-le r-type a b)
   (ftc15-tagged-division-tail-p r-type division a b)))

(defun ftc15-riemann-sum (r-type function division)
  (if (endp division)
      (ftc15-zero r-type)
    (let* ((piece (car division))
           (tag (nth 0 piece))
           (left (nth 1 piece))
           (right (nth 2 piece)))
      (ftc15-add
       r-type
       (ftc15-mul
        r-type
        (ftc15-function-value r-type function tag)
        (ftc15-sub r-type right left))
       (ftc15-riemann-sum r-type function (cdr division))))))

;; A positive gauge is an arbitrary positive real-valued function on [a,b].

(defun-sk ftc15-positive-gauge-p (r-type gauge a b)
  (forall (x)
    (implies
     (ftc15-in-closed-interval-p r-type a b x)
     (ftc15-lt
      r-type
      (ftc15-zero r-type)
      (ftc15-function-value r-type gauge x)))))

(defun ftc15-fine-tagged-division-p (r-type gauge division)
  (if (endp division)
      t
    (let* ((piece (car division))
           (tag (nth 0 piece))
           (left (nth 1 piece))
           (right (nth 2 piece))
           (gauge-at-tag
            (ftc15-function-value r-type gauge tag)))
      (and
       (ftc15-lt
        r-type
        (ftc15-sub r-type tag left)
        gauge-at-tag)
       (ftc15-lt
        r-type
        (ftc15-sub r-type right tag)
        gauge-at-tag)
       (ftc15-fine-tagged-division-p
        r-type gauge (cdr division))))))

(defun-sk ftc15-fine-tagged-division-exists-p
    (r-type gauge a b)
  (exists (division)
    (and
     (ftc15-tagged-division-p r-type a b division)
     (ftc15-fine-tagged-division-p r-type gauge division))))

(defun-sk ftc15-all-fine-sums-close-p
    (r-type function integral gauge a b epsilon)
  (forall (division)
    (implies
     (and
      (ftc15-tagged-division-p r-type a b division)
      (ftc15-fine-tagged-division-p r-type gauge division))
     (ftc15-lt
      r-type
      (ftc15-abs
       r-type
       (ftc15-sub
        r-type
        (ftc15-riemann-sum r-type function division)
        integral))
      epsilon))))

;; Fine-division existence is included with each gauge witness. Over the
;; complete real interval this is the usual Cousin property, and it makes the
;; universal condition on fine divisions explicitly non-vacuous.

(defun-sk ftc15-integral-gauge-exists-p
    (r-type function integral a b epsilon)
  (exists (gauge)
    (and
     (ftc15-real-function-p r-type gauge)
     (ftc15-positive-gauge-p r-type gauge a b)
     (ftc15-fine-tagged-division-exists-p r-type gauge a b)
     (ftc15-all-fine-sums-close-p
      r-type function integral gauge a b epsilon))))

(defun-sk ftc15-has-gauge-integral-p
    (r-type function integral a b)
  (forall (epsilon)
    (implies
     (and
      (ftc15-real-p r-type epsilon)
      (ftc15-lt r-type (ftc15-zero r-type) epsilon))
     (ftc15-integral-gauge-exists-p
      r-type function integral a b epsilon))))

(defun-sk hundred-theorems-acl2-015-statement ()
  (forall (r-type antiderivative derivative-function a b)
    (implies
     (and
      (ftc15-real-structure-p r-type)
      (ftc15-real-p r-type a)
      (ftc15-real-p r-type b)
      (ftc15-le r-type a b)
      (ftc15-real-function-p r-type antiderivative)
      (ftc15-real-function-p r-type derivative-function)
      (ftc15-derivative-on-closed-interval-p
       r-type antiderivative derivative-function a b))
     (ftc15-has-gauge-integral-p
      r-type
      derivative-function
      (ftc15-sub
       r-type
       (ftc15-function-value r-type antiderivative b)
       (ftc15-function-value r-type antiderivative a))
      a b))))

(value-triple :itpeval-statement-checked)

:q
