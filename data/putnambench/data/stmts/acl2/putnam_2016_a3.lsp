;; Statement-only formalization of PutnamBench corpus artifact putnam_2016_a3:
;; every real-valued function satisfying
;; f(x) + f(1 - 1/x) = arctan(x) for every nonzero real x has integral
;; 3*pi/8 on [0,1]. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These conservative interfaces present a real carrier, its ordered-field
;; operations, arbitrary subsets and real-valued functions, and the analytic
;; constants in the source statement.

(defstub p16a3-real-p (real-type value) t)
(defstub p16a3-zero (real-type) t)
(defstub p16a3-one (real-type) t)
(defstub p16a3-add (real-type left right) t)
(defstub p16a3-mul (real-type left right) t)
(defstub p16a3-neg (real-type value) t)
(defstub p16a3-inv (real-type value) t)
(defstub p16a3-lt (real-type left right) t)

(defstub p16a3-set-member-p (real-type set value) t)
(defstub p16a3-function-value (real-type function argument) t)

(defstub p16a3-pi (real-type) t)
(defstub p16a3-arctan (real-type value) t)

(defun p16a3-sub (real-type x y)
  (p16a3-add real-type x (p16a3-neg real-type y)))

(defun p16a3-le (real-type x y)
  (not (p16a3-lt real-type y x)))

(defun p16a3-div (real-type x y)
  (p16a3-mul real-type x (p16a3-inv real-type y)))

(defun p16a3-abs (real-type x)
  (if (p16a3-lt real-type x (p16a3-zero real-type))
      (p16a3-neg real-type x)
    x))

(defun p16a3-two (real-type)
  (p16a3-add
   real-type
   (p16a3-one real-type)
   (p16a3-one real-type)))

(defun p16a3-four (real-type)
  (p16a3-add
   real-type
   (p16a3-two real-type)
   (p16a3-two real-type)))

(defun p16a3-nat-value (real-type n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (p16a3-zero real-type)
    (p16a3-add
     real-type
     (p16a3-one real-type)
     (p16a3-nat-value real-type (1- n)))))

;; A complete Archimedean ordered-field presentation of the real numbers.

(defun-sk p16a3-operation-closure-p (real-type)
  (forall (x y)
    (and
     (p16a3-real-p real-type (p16a3-zero real-type))
     (p16a3-real-p real-type (p16a3-one real-type))
     (implies
      (p16a3-real-p real-type x)
      (and
       (p16a3-real-p real-type (p16a3-neg real-type x))
       (p16a3-real-p real-type (p16a3-inv real-type x))))
     (implies
      (and
       (p16a3-real-p real-type x)
       (p16a3-real-p real-type y))
      (and
       (p16a3-real-p real-type (p16a3-add real-type x y))
       (p16a3-real-p real-type (p16a3-mul real-type x y)))))))

(defun-sk p16a3-unary-field-laws-p (real-type)
  (forall (x)
    (implies
     (p16a3-real-p real-type x)
     (let ((zero (p16a3-zero real-type))
           (one (p16a3-one real-type)))
       (and
        (equal (p16a3-add real-type zero x) x)
        (equal (p16a3-add real-type x zero) x)
        (equal
         (p16a3-add real-type x (p16a3-neg real-type x))
         zero)
        (equal
         (p16a3-add real-type (p16a3-neg real-type x) x)
         zero)
        (equal (p16a3-mul real-type one x) x)
        (equal (p16a3-mul real-type x one) x)
        (implies
         (equal x zero)
         (equal (p16a3-inv real-type x) zero))
        (implies
         (not (equal x zero))
         (and
          (equal
           (p16a3-mul real-type x (p16a3-inv real-type x))
           one)
          (equal
           (p16a3-mul real-type (p16a3-inv real-type x) x)
           one))))))))

(defun-sk p16a3-binary-field-laws-p (real-type)
  (forall (x y)
    (implies
     (and
      (p16a3-real-p real-type x)
      (p16a3-real-p real-type y))
     (and
      (equal
       (p16a3-add real-type x y)
       (p16a3-add real-type y x))
      (equal
       (p16a3-mul real-type x y)
       (p16a3-mul real-type y x))))))

(defun-sk p16a3-ternary-field-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (p16a3-real-p real-type x)
      (p16a3-real-p real-type y)
      (p16a3-real-p real-type z))
     (and
      (equal
       (p16a3-add real-type (p16a3-add real-type x y) z)
       (p16a3-add real-type x (p16a3-add real-type y z)))
      (equal
       (p16a3-mul real-type (p16a3-mul real-type x y) z)
       (p16a3-mul real-type x (p16a3-mul real-type y z)))
      (equal
       (p16a3-mul
        real-type x (p16a3-add real-type y z))
       (p16a3-add
        real-type
        (p16a3-mul real-type x y)
        (p16a3-mul real-type x z)))))))

(defun-sk p16a3-order-laws-p (real-type)
  (forall (x y z)
    (implies
     (and
      (p16a3-real-p real-type x)
      (p16a3-real-p real-type y)
      (p16a3-real-p real-type z))
     (and
      (not (p16a3-lt real-type x x))
      (implies
       (and
        (p16a3-lt real-type x y)
        (p16a3-lt real-type y z))
       (p16a3-lt real-type x z))
      (or
       (p16a3-lt real-type x y)
       (equal x y)
       (p16a3-lt real-type y x))
      (implies
       (p16a3-lt real-type x y)
       (p16a3-lt
        real-type
        (p16a3-add real-type x z)
        (p16a3-add real-type y z)))
      (implies
       (and
        (p16a3-lt real-type (p16a3-zero real-type) x)
        (p16a3-lt real-type (p16a3-zero real-type) y))
       (p16a3-lt
        real-type
        (p16a3-zero real-type)
        (p16a3-mul real-type x y)))))))

(defun-sk p16a3-valid-real-set-p (real-type set)
  (forall (x)
    (implies
     (p16a3-set-member-p real-type set x)
     (p16a3-real-p real-type x))))

(defun-sk p16a3-set-nonempty-p (real-type set)
  (exists (x)
    (and
     (p16a3-real-p real-type x)
     (p16a3-set-member-p real-type set x))))

(defun-sk p16a3-upper-bound-p (real-type set bound)
  (forall (x)
    (implies
     (p16a3-set-member-p real-type set x)
     (p16a3-le real-type x bound))))

(defun-sk p16a3-bounded-above-p (real-type set)
  (exists (bound)
    (and
     (p16a3-real-p real-type bound)
     (p16a3-upper-bound-p real-type set bound))))

(defun-sk p16a3-least-upper-bound-p
    (real-type set supremum)
  (forall (bound)
    (and
     (p16a3-real-p real-type supremum)
     (p16a3-upper-bound-p real-type set supremum)
     (implies
      (and
       (p16a3-real-p real-type bound)
       (p16a3-upper-bound-p real-type set bound))
      (p16a3-le real-type supremum bound)))))

(defun-sk p16a3-supremum-exists-p (real-type set)
  (exists (supremum)
    (p16a3-least-upper-bound-p real-type set supremum)))

(defun-sk p16a3-dedekind-complete-p (real-type)
  (forall (set)
    (implies
     (and
      (p16a3-valid-real-set-p real-type set)
      (p16a3-set-nonempty-p real-type set)
      (p16a3-bounded-above-p real-type set))
     (p16a3-supremum-exists-p real-type set))))

(defun-sk p16a3-archimedean-witness-p (real-type x)
  (exists (n)
    (and
     (natp n)
     (p16a3-lt
      real-type x (p16a3-nat-value real-type n)))))

(defun-sk p16a3-archimedean-p (real-type)
  (forall (x)
    (implies
     (p16a3-real-p real-type x)
     (p16a3-archimedean-witness-p real-type x))))

(defun p16a3-real-structure-p (real-type)
  (and
   (p16a3-operation-closure-p real-type)
   (p16a3-unary-field-laws-p real-type)
   (p16a3-binary-field-laws-p real-type)
   (p16a3-ternary-field-laws-p real-type)
   (p16a3-order-laws-p real-type)
   (not
    (equal
     (p16a3-zero real-type)
     (p16a3-one real-type)))
   (p16a3-lt
    real-type
    (p16a3-zero real-type)
    (p16a3-one real-type))
   (p16a3-dedekind-complete-p real-type)
   (p16a3-archimedean-p real-type)))

;; Arbitrary functions are represented extensionally by their values on the
;; unbounded real carrier; no finite table or bounded domain is used.

(defun-sk p16a3-real-function-p (real-type function)
  (forall (x)
    (implies
     (p16a3-real-p real-type x)
     (p16a3-real-p
      real-type
      (p16a3-function-value real-type function x)))))

;; Exact gauge integrals. A tagged division is an intrinsically finite list of
;; triples (tag, left endpoint, right endpoint), but all real and functional
;; quantifiers remain unrestricted.

(defun p16a3-in-closed-interval-p (real-type a b x)
  (and
   (p16a3-real-p real-type x)
   (p16a3-le real-type a x)
   (p16a3-le real-type x b)))

(defun p16a3-integrand-value (real-type kind function x)
  (if (equal kind :arctan-kernel)
      (p16a3-inv
       real-type
       (p16a3-add
        real-type
        (p16a3-one real-type)
        (p16a3-mul real-type x x)))
    (if (equal kind :source-function)
        (p16a3-function-value real-type function x)
      (p16a3-zero real-type))))

(defun p16a3-tagged-piece-p (real-type piece)
  (and
   (true-listp piece)
   (equal (len piece) 3)
   (p16a3-real-p real-type (nth 0 piece))
   (p16a3-real-p real-type (nth 1 piece))
   (p16a3-real-p real-type (nth 2 piece))
   (p16a3-lt real-type (nth 1 piece) (nth 2 piece))
   (p16a3-le real-type (nth 1 piece) (nth 0 piece))
   (p16a3-le real-type (nth 0 piece) (nth 2 piece))))

(defun p16a3-tagged-division-tail-p
    (real-type division next-left b)
  (if (endp division)
      (equal next-left b)
    (let ((piece (car division)))
      (and
       (p16a3-tagged-piece-p real-type piece)
       (equal (nth 1 piece) next-left)
       (p16a3-tagged-division-tail-p
        real-type
        (cdr division)
        (nth 2 piece)
        b)))))

(defun p16a3-tagged-division-p
    (real-type a b division)
  (and
   (true-listp division)
   (p16a3-real-p real-type a)
   (p16a3-real-p real-type b)
   (p16a3-le real-type a b)
   (p16a3-tagged-division-tail-p
    real-type division a b)))

(defun p16a3-riemann-sum
    (real-type kind function division)
  (if (endp division)
      (p16a3-zero real-type)
    (let* ((piece (car division))
           (tag (nth 0 piece))
           (left (nth 1 piece))
           (right (nth 2 piece)))
      (p16a3-add
       real-type
       (p16a3-mul
        real-type
        (p16a3-integrand-value
         real-type kind function tag)
        (p16a3-sub real-type right left))
       (p16a3-riemann-sum
        real-type kind function (cdr division))))))

(defun-sk p16a3-positive-gauge-p
    (real-type gauge a b)
  (forall (x)
    (implies
     (p16a3-in-closed-interval-p real-type a b x)
     (p16a3-lt
      real-type
      (p16a3-zero real-type)
      (p16a3-function-value real-type gauge x)))))

(defun p16a3-fine-tagged-division-p
    (real-type gauge division)
  (if (endp division)
      t
    (let* ((piece (car division))
           (tag (nth 0 piece))
           (left (nth 1 piece))
           (right (nth 2 piece))
           (radius
            (p16a3-function-value real-type gauge tag)))
      (and
       (p16a3-lt
        real-type
        (p16a3-sub real-type tag left)
        radius)
       (p16a3-lt
        real-type
        (p16a3-sub real-type right tag)
        radius)
       (p16a3-fine-tagged-division-p
        real-type gauge (cdr division))))))

(defun-sk p16a3-fine-division-exists-p
    (real-type gauge a b)
  (exists (division)
    (and
     (p16a3-tagged-division-p
      real-type a b division)
     (p16a3-fine-tagged-division-p
      real-type gauge division))))

(defun-sk p16a3-all-fine-sums-close-p
    (real-type kind function integral gauge a b epsilon)
  (forall (division)
    (implies
     (and
      (p16a3-tagged-division-p
       real-type a b division)
      (p16a3-fine-tagged-division-p
       real-type gauge division))
     (p16a3-lt
      real-type
      (p16a3-abs
       real-type
       (p16a3-sub
        real-type
        (p16a3-riemann-sum
         real-type kind function division)
        integral))
      epsilon))))

(defun-sk p16a3-integral-gauge-exists-p
    (real-type kind function integral a b epsilon)
  (exists (gauge)
    (and
     (p16a3-real-function-p real-type gauge)
     (p16a3-positive-gauge-p real-type gauge a b)
     (p16a3-fine-division-exists-p
      real-type gauge a b)
     (p16a3-all-fine-sums-close-p
      real-type kind function integral gauge a b epsilon))))

(defun-sk p16a3-has-gauge-integral-p
    (real-type kind function integral a b)
  (forall (epsilon)
    (implies
     (and
      (p16a3-real-p real-type epsilon)
      (p16a3-lt
       real-type
       (p16a3-zero real-type)
       epsilon))
     (and
      (p16a3-real-p real-type integral)
      (p16a3-integral-gauge-exists-p
       real-type kind function integral a b epsilon)))))

;; Arctangent is independently fixed on every real argument by the exact
;; integral of 1/(1+x^2), using oddness through an oriented positive interval
;; for negative arguments. Pi is then the standard value 4*arctan(1).

(defun-sk p16a3-arctan-definition-p (real-type)
  (forall (y)
    (implies
     (p16a3-real-p real-type y)
     (and
      (p16a3-real-p
       real-type (p16a3-arctan real-type y))
      (if (p16a3-lt
           real-type y (p16a3-zero real-type))
          (p16a3-has-gauge-integral-p
           real-type
           :arctan-kernel
           nil
           (p16a3-neg
            real-type (p16a3-arctan real-type y))
           (p16a3-zero real-type)
           (p16a3-neg real-type y))
        (p16a3-has-gauge-integral-p
         real-type
         :arctan-kernel
         nil
         (p16a3-arctan real-type y)
         (p16a3-zero real-type)
         y))))))

(defun p16a3-pi-definition-p (real-type)
  (let ((pi-value (p16a3-pi real-type))
        (one (p16a3-one real-type)))
    (and
     (p16a3-real-p real-type pi-value)
     (p16a3-lt real-type (p16a3-zero real-type) pi-value)
     (equal
      pi-value
      (p16a3-mul
       real-type
       (p16a3-four real-type)
       (p16a3-arctan real-type one))))))

;; This is the source hypothesis, with its original nonzero-real quantifier.

(defun-sk p16a3-functional-equation-p
    (real-type function)
  (forall (x)
    (implies
     (and
      (p16a3-real-p real-type x)
      (not (equal x (p16a3-zero real-type))))
     (equal
      (p16a3-add
       real-type
       (p16a3-function-value real-type function x)
       (p16a3-function-value
        real-type
        function
        (p16a3-sub
         real-type
         (p16a3-one real-type)
         (p16a3-inv real-type x))))
      (p16a3-arctan real-type x)))))

(defun p16a3-solution (real-type)
  (p16a3-div
   real-type
   (p16a3-mul
    real-type
    (p16a3-nat-value real-type 3)
    (p16a3-pi real-type))
   (p16a3-nat-value real-type 8)))

(defun-sk putnambench-putnam-2016-a3-statement ()
  (forall (real-type function)
    (implies
     (and
      (p16a3-real-structure-p real-type)
      (p16a3-arctan-definition-p real-type)
      (p16a3-pi-definition-p real-type)
      (p16a3-real-function-p real-type function)
      (p16a3-functional-equation-p real-type function))
     (p16a3-has-gauge-integral-p
      real-type
      :source-function
      function
      (p16a3-solution real-type)
      (p16a3-zero real-type)
      (p16a3-one real-type)))))

(value-triple :itpeval-statement-checked)

:q
