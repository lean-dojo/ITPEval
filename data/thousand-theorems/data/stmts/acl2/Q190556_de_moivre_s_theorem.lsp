;; Statement-only formalization of thousand-theorems corpus artifact Q190556,
;; "De Moivre's theorem": for every natural n and complex z, the nth power
;; of cos(z) + sin(z)*i equals cos(n*z) + sin(n*z)*i. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A Dedekind-complete ordered field presents the real numbers. Complex
;; numbers are explicit real/imaginary pairs, with their usual field
;; operations. The sine and cosine interfaces are fixed to the standard
;; entire functions by convergence of their full power series. Thus the
;; statement below retains the source's natural and complex quantifiers and
;; its pointwise equality, rather than replacing it by a bounded or
;; coefficient-only surrogate.

(defstub q190556-r-member-p (real value) t)
(defstub q190556-r-zero (real) t)
(defstub q190556-r-one (real) t)
(defstub q190556-r-add (real left right) t)
(defstub q190556-r-multiply (real left right) t)
(defstub q190556-r-negate (real value) t)
(defstub q190556-r-inverse (real value) t)
(defstub q190556-r-less (real left right) t)
(defstub q190556-r-set-member-p (real set value) t)

(defstub q190556-cos (real value) t)
(defstub q190556-sin (real value) t)

(defun q190556-r-subtract (real left right)
  (q190556-r-add
   real left (q190556-r-negate real right)))

(defun q190556-r-absolute-value (real value)
  (if (q190556-r-less
       real value (q190556-r-zero real))
      (q190556-r-negate real value)
    value))

(defun q190556-r-positive-p (real value)
  (and
   (q190556-r-member-p real value)
   (q190556-r-less
    real (q190556-r-zero real) value)))

(defun q190556-r-leq (real left right)
  (not (q190556-r-less real right left)))

(defun-sk q190556-r-field-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q190556-r-member-p real x)
      (q190556-r-member-p real y)
      (q190556-r-member-p real z))
     (let* ((zero (q190556-r-zero real))
            (one (q190556-r-one real))
            (xy-add (q190556-r-add real x y))
            (yz-add (q190556-r-add real y z))
            (xy-mul (q190556-r-multiply real x y))
            (yz-mul (q190556-r-multiply real y z))
            (neg-x (q190556-r-negate real x))
            (inv-x (q190556-r-inverse real x)))
       (and
        (q190556-r-member-p real xy-add)
        (q190556-r-member-p real xy-mul)
        (q190556-r-member-p real neg-x)
        (q190556-r-member-p real inv-x)
        (equal
         (q190556-r-add real xy-add z)
         (q190556-r-add real x yz-add))
        (equal xy-add (q190556-r-add real y x))
        (equal (q190556-r-add real x zero) x)
        (equal (q190556-r-add real x neg-x) zero)
        (equal
         (q190556-r-multiply real xy-mul z)
         (q190556-r-multiply real x yz-mul))
        (equal xy-mul (q190556-r-multiply real y x))
        (equal (q190556-r-multiply real x one) x)
        (implies
         (equal x zero)
         (equal inv-x zero))
        (implies
         (not (equal x zero))
         (equal
          (q190556-r-multiply real x inv-x)
          one))
        (equal
         (q190556-r-multiply real x yz-add)
         (q190556-r-add
          real
          (q190556-r-multiply real x y)
          (q190556-r-multiply real x z))))))))

(defun-sk q190556-r-order-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q190556-r-member-p real x)
      (q190556-r-member-p real y)
      (q190556-r-member-p real z))
     (let ((zero (q190556-r-zero real)))
       (and
        (not (q190556-r-less real x x))
        (or
         (equal x y)
         (q190556-r-less real x y)
         (q190556-r-less real y x))
        (implies
         (and
          (q190556-r-less real x y)
          (q190556-r-less real y z))
         (q190556-r-less real x z))
        (implies
         (q190556-r-less real x y)
         (q190556-r-less
          real
          (q190556-r-add real x z)
          (q190556-r-add real y z)))
        (implies
         (and
          (q190556-r-less real zero x)
          (q190556-r-less real zero y))
         (q190556-r-less
          real zero
          (q190556-r-multiply real x y))))))))

(defun-sk q190556-r-set-nonempty-p (real set)
  (exists (x)
    (and
     (q190556-r-member-p real x)
     (q190556-r-set-member-p real set x))))

(defun-sk q190556-r-upper-bound-p (real set bound)
  (forall (x)
    (implies
     (and
      (q190556-r-member-p real x)
      (q190556-r-set-member-p real set x))
     (q190556-r-leq real x bound))))

(defun-sk q190556-r-bounded-above-p (real set)
  (exists (bound)
    (and
     (q190556-r-member-p real bound)
     (q190556-r-upper-bound-p real set bound))))

(defun-sk q190556-r-supremum-p (real set supremum)
  (forall (bound)
    (and
     (q190556-r-member-p real supremum)
     (q190556-r-upper-bound-p real set supremum)
     (implies
      (and
       (q190556-r-member-p real bound)
       (q190556-r-upper-bound-p real set bound))
      (q190556-r-leq real supremum bound)))))

(defun-sk q190556-r-has-supremum-p (real set)
  (exists (supremum)
    (q190556-r-supremum-p real set supremum)))

(defun-sk q190556-r-dedekind-complete-p (real)
  (forall (set)
    (implies
     (and
      (q190556-r-set-nonempty-p real set)
      (q190556-r-bounded-above-p real set))
     (q190556-r-has-supremum-p real set))))

(defun q190556-real-field-p (real)
  (let ((zero (q190556-r-zero real))
        (one (q190556-r-one real)))
    (and
     (q190556-r-member-p real zero)
     (q190556-r-member-p real one)
     (not (equal zero one))
     (q190556-r-field-laws-p real)
     (q190556-r-order-laws-p real)
     (q190556-r-less real zero one)
     (q190556-r-dedekind-complete-p real))))

;; Complex arithmetic over the presented real field.

(defun q190556-c-member-p (real value)
  (and
   (consp value)
   (q190556-r-member-p real (car value))
   (q190556-r-member-p real (cdr value))))

(defun q190556-c-zero (real)
  (cons (q190556-r-zero real)
        (q190556-r-zero real)))

(defun q190556-c-one (real)
  (cons (q190556-r-one real)
        (q190556-r-zero real)))

(defun q190556-c-I (real)
  (cons (q190556-r-zero real)
        (q190556-r-one real)))

(defun q190556-c-of-real (real value)
  (cons value (q190556-r-zero real)))

(defun q190556-c-add (real left right)
  (cons
   (q190556-r-add real (car left) (car right))
   (q190556-r-add real (cdr left) (cdr right))))

(defun q190556-c-negate (real value)
  (cons
   (q190556-r-negate real (car value))
   (q190556-r-negate real (cdr value))))

(defun q190556-c-subtract (real left right)
  (q190556-c-add
   real left (q190556-c-negate real right)))

(defun q190556-c-multiply (real left right)
  (let ((a (car left))
        (b (cdr left))
        (c (car right))
        (d (cdr right)))
    (cons
     (q190556-r-subtract
      real
      (q190556-r-multiply real a c)
      (q190556-r-multiply real b d))
     (q190556-r-add
      real
      (q190556-r-multiply real a d)
      (q190556-r-multiply real b c)))))

(defun q190556-r-nat (real n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q190556-r-zero real)
    (q190556-r-add
     real
     (q190556-r-one real)
     (q190556-r-nat real (- n 1)))))

(defun q190556-r-factorial (real n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q190556-r-one real)
    (q190556-r-multiply
     real
     (q190556-r-nat real n)
     (q190556-r-factorial real (- n 1)))))

(defun q190556-c-power (real base exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (q190556-c-one real)
    (q190556-c-multiply
     real
     base
     (q190556-c-power real base (- exponent 1)))))

;; Canonical Taylor coefficients and partial sums for complex cosine and sine.

(defun q190556-r-alternating-unit (real index)
  (if (evenp index)
      (q190556-r-one real)
    (q190556-r-negate real (q190556-r-one real))))

(defun q190556-r-series-coefficient
    (real degree)
  (q190556-r-multiply
   real
   (q190556-r-alternating-unit
    real (floor degree 2))
   (q190556-r-inverse
    real (q190556-r-factorial real degree))))

(defun q190556-cosine-term (real z degree)
  (if (and (natp degree) (evenp degree))
      (q190556-c-multiply
       real
       (q190556-c-of-real
        real
        (q190556-r-series-coefficient real degree))
       (q190556-c-power real z degree))
    (q190556-c-zero real)))

(defun q190556-sine-term (real z degree)
  (if (and (natp degree) (oddp degree))
      (q190556-c-multiply
       real
       (q190556-c-of-real
        real
        (q190556-r-series-coefficient real degree))
       (q190556-c-power real z degree))
    (q190556-c-zero real)))

(defun q190556-cosine-prefix (real z terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      (q190556-c-zero real)
    (let ((degree (- terms 1)))
      (q190556-c-add
       real
       (q190556-cosine-prefix real z degree)
       (q190556-cosine-term real z degree)))))

(defun q190556-sine-prefix (real z terms)
  (declare (xargs :measure (nfix terms)))
  (if (zp terms)
      (q190556-c-zero real)
    (let ((degree (- terms 1)))
      (q190556-c-add
       real
       (q190556-sine-prefix real z degree)
       (q190556-sine-term real z degree)))))

(defun q190556-c-close-p (real left right epsilon)
  (and
   (q190556-r-less
    real
    (q190556-r-absolute-value
     real
     (q190556-r-subtract
      real (car left) (car right)))
    epsilon)
   (q190556-r-less
    real
    (q190556-r-absolute-value
     real
     (q190556-r-subtract
      real (cdr left) (cdr right)))
    epsilon)))

(defun-sk q190556-cosine-tail-p
    (real z epsilon cutoff)
  (forall (terms)
    (implies
     (and
      (natp terms)
      (natp cutoff)
      (<= cutoff terms))
     (q190556-c-close-p
      real
      (q190556-cosine-prefix real z terms)
      (q190556-cos real z)
      epsilon))))

(defun-sk q190556-cosine-cutoff-exists-p
    (real z epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (q190556-cosine-tail-p
      real z epsilon cutoff))))

(defun-sk q190556-cosine-converges-at-p (real z)
  (forall (epsilon)
    (implies
     (q190556-r-positive-p real epsilon)
     (q190556-cosine-cutoff-exists-p
      real z epsilon))))

(defun q190556-cosine-value-p (real z)
  (and
   (q190556-c-member-p real (q190556-cos real z))
   (q190556-cosine-converges-at-p real z)))

(defun-sk q190556-cosine-series-laws-p (real)
  (forall (z)
    (implies
     (q190556-c-member-p real z)
     (q190556-cosine-value-p real z))))

(defun-sk q190556-sine-tail-p
    (real z epsilon cutoff)
  (forall (terms)
    (implies
     (and
      (natp terms)
      (natp cutoff)
      (<= cutoff terms))
     (q190556-c-close-p
      real
      (q190556-sine-prefix real z terms)
      (q190556-sin real z)
      epsilon))))

(defun-sk q190556-sine-cutoff-exists-p
    (real z epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (q190556-sine-tail-p
      real z epsilon cutoff))))

(defun-sk q190556-sine-converges-at-p (real z)
  (forall (epsilon)
    (implies
     (q190556-r-positive-p real epsilon)
     (q190556-sine-cutoff-exists-p
      real z epsilon))))

(defun q190556-sine-value-p (real z)
  (and
   (q190556-c-member-p real (q190556-sin real z))
   (q190556-sine-converges-at-p real z)))

(defun-sk q190556-sine-series-laws-p (real)
  (forall (z)
    (implies
     (q190556-c-member-p real z)
     (q190556-sine-value-p real z))))

(defun q190556-de-moivre-identity-p (real n z)
  (let* ((imaginary-unit (q190556-c-I real))
         (cis-z
          (q190556-c-add
           real
           (q190556-cos real z)
           (q190556-c-multiply
            real
            (q190556-sin real z)
            imaginary-unit)))
         (real-n (q190556-r-nat real n))
         (n-times-z
          (q190556-c-multiply
           real
           (q190556-c-of-real real real-n)
           z)))
    (equal
     (q190556-c-power real cis-z n)
     (q190556-c-add
      real
      (q190556-cos real n-times-z)
      (q190556-c-multiply
       real
       (q190556-sin real n-times-z)
       imaginary-unit)))))

(defun-sk
    thousand-theorems-q190556-de-moivre-s-theorem-statement
    ()
  (forall (real n z)
    (implies
     (and
      (q190556-real-field-p real)
      (q190556-cosine-series-laws-p real)
      (q190556-sine-series-laws-p real)
      (natp n)
      (q190556-c-member-p real z))
     (q190556-de-moivre-identity-p real n z))))

(value-triple :itpeval-statement-checked)
:q
