;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/binary_sqrt_BinarySqrt_sqrtqtvc: the binary-square-root verification
;; condition for one refinement step over nonnegative real inputs.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Real-valued variables range over an arbitrary real closed ordered field.
;; The separate integer embedding and ceiling laws below interpret the source
;; real_of_int and mathematical ceil operations without restricting reals to
;; ACL2's rational numbers.

(defstub sqrtvc-real-op (ctx x) t)
(defstub sqrtvc-add-op (ctx x y) t)
(defstub sqrtvc-mul-op (ctx x y) t)
(defstub sqrtvc-neg-op (ctx x) t)
(defstub sqrtvc-inv-op (ctx x) t)
(defstub sqrtvc-lt-op (ctx x y) t)
(defstub sqrtvc-int-embed-op (ctx n) t)
(defstub sqrtvc-ceil-op (ctx x) t)

(defun sqrtvc-real-p (ctx x)
  (if (sqrtvc-real-op ctx x) t nil))

(defun sqrtvc-add (ctx x y)
  (sqrtvc-add-op ctx x y))

(defun sqrtvc-mul (ctx x y)
  (sqrtvc-mul-op ctx x y))

(defun sqrtvc-neg (ctx x)
  (sqrtvc-neg-op ctx x))

(defun sqrtvc-inv (ctx x)
  (sqrtvc-inv-op ctx x))

(defun sqrtvc-lt (ctx x y)
  (if (sqrtvc-lt-op ctx x y) t nil))

(defun sqrtvc-le (ctx x y)
  (not (sqrtvc-lt ctx y x)))

(defun sqrtvc-int-embed (ctx n)
  (sqrtvc-int-embed-op ctx n))

(defun sqrtvc-ceil (ctx x)
  (sqrtvc-ceil-op ctx x))

(defun sqrtvc-div (ctx x y)
  (sqrtvc-mul ctx x (sqrtvc-inv ctx y)))

(defun sqrtvc-max (ctx x y)
  (if (sqrtvc-lt ctx x y) y x))

(defun-sk sqrtvc-field-laws-p (ctx zero one)
  (forall (x y z)
    (implies
     (and
      (sqrtvc-real-p ctx x)
      (sqrtvc-real-p ctx y)
      (sqrtvc-real-p ctx z))
     (and
      (sqrtvc-real-p ctx (sqrtvc-add ctx x y))
      (sqrtvc-real-p ctx (sqrtvc-mul ctx x y))
      (sqrtvc-real-p ctx (sqrtvc-neg ctx x))
      (sqrtvc-real-p ctx (sqrtvc-inv ctx x))
      (equal
       (sqrtvc-add ctx (sqrtvc-add ctx x y) z)
       (sqrtvc-add ctx x (sqrtvc-add ctx y z)))
      (equal (sqrtvc-add ctx x y) (sqrtvc-add ctx y x))
      (equal (sqrtvc-add ctx x zero) x)
      (equal (sqrtvc-add ctx x (sqrtvc-neg ctx x)) zero)
      (equal
       (sqrtvc-mul ctx (sqrtvc-mul ctx x y) z)
       (sqrtvc-mul ctx x (sqrtvc-mul ctx y z)))
      (equal (sqrtvc-mul ctx x y) (sqrtvc-mul ctx y x))
      (equal (sqrtvc-mul ctx x one) x)
      (equal (sqrtvc-inv ctx zero) zero)
      (implies
       (not (equal x zero))
       (equal (sqrtvc-mul ctx x (sqrtvc-inv ctx x)) one))
      (equal
       (sqrtvc-mul ctx x (sqrtvc-add ctx y z))
       (sqrtvc-add
        ctx
        (sqrtvc-mul ctx x y)
        (sqrtvc-mul ctx x z)))))))

(defun-sk sqrtvc-order-laws-p (ctx zero)
  (forall (x y z)
    (implies
     (and
      (sqrtvc-real-p ctx x)
      (sqrtvc-real-p ctx y)
      (sqrtvc-real-p ctx z))
     (and
      (not (sqrtvc-lt ctx x x))
      (or
       (equal x y)
       (sqrtvc-lt ctx x y)
       (sqrtvc-lt ctx y x))
      (implies
       (and
        (sqrtvc-lt ctx x y)
        (sqrtvc-lt ctx y z))
       (sqrtvc-lt ctx x z))
      (implies
       (sqrtvc-lt ctx x y)
       (sqrtvc-lt
        ctx
        (sqrtvc-add ctx x z)
        (sqrtvc-add ctx y z)))
      (implies
       (and
        (sqrtvc-lt ctx zero x)
        (sqrtvc-lt ctx zero y))
       (sqrtvc-lt ctx zero (sqrtvc-mul ctx x y)))))))

(defun-sk sqrtvc-positive-square-root-exists-p
    (ctx zero x)
  (exists (root)
    (and
     (sqrtvc-real-p ctx root)
     (sqrtvc-le ctx zero root)
     (equal (sqrtvc-mul ctx root root) x))))

(defun-sk sqrtvc-positive-square-root-laws-p (ctx zero)
  (forall (x)
    (implies
     (and
      (sqrtvc-real-p ctx x)
      (sqrtvc-lt ctx zero x))
     (sqrtvc-positive-square-root-exists-p
      ctx zero x))))

(defun sqrtvc-real-coefficient-list-p (ctx coefficients)
  (if (consp coefficients)
      (and
       (sqrtvc-real-p ctx (car coefficients))
       (sqrtvc-real-coefficient-list-p
        ctx (cdr coefficients)))
    (equal coefficients nil)))

(defun sqrtvc-poly-eval (ctx zero coefficients x)
  (if (consp coefficients)
      (sqrtvc-add
       ctx
       (car coefficients)
       (sqrtvc-mul
        ctx
        x
        (sqrtvc-poly-eval
         ctx zero (cdr coefficients) x)))
    zero))

(defun-sk sqrtvc-odd-polynomial-root-exists-p
    (ctx zero coefficients)
  (exists (root)
    (and
     (sqrtvc-real-p ctx root)
     (equal
      (sqrtvc-poly-eval ctx zero coefficients root)
      zero))))

(defun-sk sqrtvc-odd-root-laws-p (ctx zero)
  (forall (coefficients degree)
    (implies
     (and
      (natp degree)
      (not (equal degree 0))
      (oddp degree)
      (true-listp coefficients)
      (consp coefficients)
      (equal (len coefficients) (+ 1 degree))
      (sqrtvc-real-coefficient-list-p ctx coefficients)
      (not (equal (car (last coefficients)) zero)))
     (sqrtvc-odd-polynomial-root-exists-p
      ctx zero coefficients))))

(defun sqrtvc-real-context-p (ctx zero one)
  (and
   (sqrtvc-real-p ctx zero)
   (sqrtvc-real-p ctx one)
   (not (equal zero one))
   (sqrtvc-lt ctx zero one)
   (sqrtvc-field-laws-p ctx zero one)
   (sqrtvc-order-laws-p ctx zero)
   (sqrtvc-positive-square-root-laws-p ctx zero)
   (sqrtvc-odd-root-laws-p ctx zero)))

;; These laws make sqrtvc-int-embed the usual ordered-ring embedding of all
;; mathematical integers into the real field.

(defun-sk sqrtvc-int-embedding-laws-p (ctx zero one)
  (forall (m n)
    (implies
     (and (integerp m) (integerp n))
     (and
      (sqrtvc-real-p ctx (sqrtvc-int-embed ctx m))
      (sqrtvc-real-p ctx (sqrtvc-int-embed ctx n))
      (equal (sqrtvc-int-embed ctx 0) zero)
      (equal (sqrtvc-int-embed ctx 1) one)
      (equal
       (sqrtvc-int-embed ctx (+ m n))
       (sqrtvc-add
        ctx
        (sqrtvc-int-embed ctx m)
        (sqrtvc-int-embed ctx n)))
      (equal
       (sqrtvc-int-embed ctx (* m n))
       (sqrtvc-mul
        ctx
        (sqrtvc-int-embed ctx m)
        (sqrtvc-int-embed ctx n)))
      (equal
       (sqrtvc-int-embed ctx (- m))
       (sqrtvc-neg ctx (sqrtvc-int-embed ctx m)))
      (equal
       (if (< m n) t nil)
       (sqrtvc-lt
        ctx
        (sqrtvc-int-embed ctx m)
        (sqrtvc-int-embed ctx n)))))))

;; This is the exact mathematical ceiling characterization:
;; ceil(x) is the integer k such that k - 1 < x <= k.

(defun-sk sqrtvc-ceil-laws-p (ctx)
  (forall (x)
    (implies
     (sqrtvc-real-p ctx x)
     (let ((k (sqrtvc-ceil ctx x)))
       (and
        (integerp k)
        (sqrtvc-lt
         ctx
         (sqrtvc-int-embed ctx (- k 1))
         x)
        (sqrtvc-le
         ctx
         x
         (sqrtvc-int-embed ctx k)))))))

(defun sqrtvc-scaled-step (ctx eps n)
  (sqrtvc-mul ctx (sqrtvc-int-embed ctx n) eps))

(defun sqrtvc-square (ctx x)
  (sqrtvc-mul ctx x x))

(defun sqrtvc-first-conclusion-p
    (ctx zero one r eps n o1)
  (implies
   (not (equal o1 t))
   (let* ((two (sqrtvc-int-embed ctx 2))
          (o2 (* 2 n))
          (ceil-value
           (sqrtvc-ceil
            ctx
            (sqrtvc-div
             ctx
             (sqrtvc-max ctx r one)
             eps)))
          (n-eps (sqrtvc-scaled-step ctx eps n)))
     (and
      (and
       (<= 0 (- ceil-value n))
       (< (- ceil-value o2)
          (- ceil-value n)))
      (sqrtvc-le ctx zero r)
      (and
       (sqrtvc-lt ctx zero eps)
       (<= 1 o2))
      (equal
       (sqrtvc-mul ctx two n-eps)
       (sqrtvc-mul
        ctx
        (sqrtvc-int-embed ctx o2)
        eps))))))

(defun-sk sqrtvc-step-result-exists-p
    (ctx r eps n result)
  (exists (r-prime)
    (and
     (sqrtvc-real-p ctx r-prime)
     (let* ((n-eps (sqrtvc-scaled-step ctx eps n))
            (two (sqrtvc-int-embed ctx 2))
            (o2 (sqrtvc-mul ctx two n-eps))
            (r-prime-plus-o2
             (sqrtvc-add ctx r-prime o2))
            (candidate
             (sqrtvc-add ctx r-prime n-eps)))
       (and
        (and
         (sqrtvc-le
          ctx
          (sqrtvc-square ctx r-prime)
          r)
         (sqrtvc-lt
          ctx
          r
          (sqrtvc-square ctx r-prime-plus-o2)))
        (if
            (sqrtvc-le
             ctx
             (sqrtvc-square ctx candidate)
             r)
            (equal result candidate)
          (equal result r-prime)))))))

(defun sqrtvc-result-premise-p
    (ctx zero r eps n o1 result)
  (if (equal o1 t)
      (equal result zero)
    (sqrtvc-step-result-exists-p
     ctx r eps n result)))

(defun sqrtvc-result-conclusion-p
    (ctx r eps n result)
  (let ((result-plus-step
         (sqrtvc-add
          ctx
          result
          (sqrtvc-scaled-step ctx eps n))))
    (and
     (sqrtvc-le
      ctx
      (sqrtvc-square ctx result)
      r)
     (sqrtvc-lt
      ctx
      r
      (sqrtvc-square ctx result-plus-step)))))

(defun-sk sqrtvc-all-results-p
    (ctx zero r eps n o1)
  (forall (result)
    (implies
     (sqrtvc-real-p ctx result)
     (implies
      (sqrtvc-result-premise-p
       ctx zero r eps n o1 result)
      (sqrtvc-result-conclusion-p
       ctx r eps n result)))))

(defun sqrtvc-fact3-p (ctx one r eps n o1)
  (let ((n-eps (sqrtvc-scaled-step ctx eps n)))
    (if (sqrtvc-lt ctx r n-eps)
        (equal
         o1
         (if (sqrtvc-lt ctx one n-eps)
             t
           nil))
      (equal o1 nil))))

(defun ntp4vc-pearl-binary-sqrt-binarysqrt-sqrtqtvc-statement
    (ctx zero one r eps n o1)
  (implies
   (and
    (sqrtvc-real-context-p ctx zero one)
    (sqrtvc-int-embedding-laws-p ctx zero one)
    (sqrtvc-ceil-laws-p ctx)
    (sqrtvc-real-p ctx r)
    (sqrtvc-real-p ctx eps)
    (integerp n)
    (booleanp o1)
    (sqrtvc-le ctx zero r)
    (sqrtvc-lt ctx zero eps)
    (<= 1 n)
    (sqrtvc-fact3-p ctx one r eps n o1))
   (and
    (sqrtvc-first-conclusion-p
     ctx zero one r eps n o1)
    (sqrtvc-all-results-p
     ctx zero r eps n o1))))

(value-triple :itpeval-statement-checked)
:q
