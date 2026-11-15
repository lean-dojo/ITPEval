;; Statement-only formalization of thousand-theorems corpus artifact Q7208500,
;; "Poisson limit theorem": for each fixed natural k, if n times the real
;; sequence p(n) converges to r, then the corresponding binomial-expression
;; term converges to exp(-r) times r^k divided by k!. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

;; An arbitrary Dedekind-complete ordered field presents the real numbers.
;; The exponential operation is characterized by convergence of its complete
;; power series. Natural casts, powers, factorials, and binomial coefficients
;; below are exact recursive operations, while both limits use their full
;; epsilon-N definitions over unbounded natural indices.

(defstub q7208500-r-member-p (real value) t)
(defstub q7208500-r-zero (real) t)
(defstub q7208500-r-one (real) t)
(defstub q7208500-r-add (real left right) t)
(defstub q7208500-r-multiply (real left right) t)
(defstub q7208500-r-negate (real value) t)
(defstub q7208500-r-inverse (real value) t)
(defstub q7208500-r-less (real left right) t)
(defstub q7208500-r-generic-set-member-p (real set value) t)
(defstub q7208500-r-exponential (real value) t)
(defstub q7208500-sequence-value (sequence index) t)

(defun q7208500-r-subtract (real left right)
  (q7208500-r-add
   real left (q7208500-r-negate real right)))

(defun q7208500-r-divide (real numerator denominator)
  (q7208500-r-multiply
   real numerator (q7208500-r-inverse real denominator)))

(defun q7208500-r-leq (real left right)
  (not (q7208500-r-less real right left)))

(defun q7208500-r-absolute-value (real value)
  (if (q7208500-r-less
       real value (q7208500-r-zero real))
      (q7208500-r-negate real value)
    value))

(defun q7208500-r-positive-p (real value)
  (and
   (q7208500-r-member-p real value)
   (q7208500-r-less
    real (q7208500-r-zero real) value)))

;; Complete ordered-field presentation of the real scalar domain.

(defun-sk q7208500-r-field-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q7208500-r-member-p real x)
      (q7208500-r-member-p real y)
      (q7208500-r-member-p real z))
     (let* ((zero (q7208500-r-zero real))
            (one (q7208500-r-one real))
            (xy-add (q7208500-r-add real x y))
            (yz-add (q7208500-r-add real y z))
            (xy-mul (q7208500-r-multiply real x y))
            (yz-mul (q7208500-r-multiply real y z))
            (neg-x (q7208500-r-negate real x))
            (inv-x (q7208500-r-inverse real x)))
       (and
        (q7208500-r-member-p real zero)
        (q7208500-r-member-p real one)
        (q7208500-r-member-p real xy-add)
        (q7208500-r-member-p real xy-mul)
        (q7208500-r-member-p real neg-x)
        (q7208500-r-member-p real inv-x)
        (equal
         (q7208500-r-add real xy-add z)
         (q7208500-r-add real x yz-add))
        (equal xy-add (q7208500-r-add real y x))
        (equal (q7208500-r-add real x zero) x)
        (equal (q7208500-r-add real x neg-x) zero)
        (equal
         (q7208500-r-multiply real xy-mul z)
         (q7208500-r-multiply real x yz-mul))
        (equal xy-mul (q7208500-r-multiply real y x))
        (equal (q7208500-r-multiply real x one) x)
        (equal (q7208500-r-inverse real zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (q7208500-r-multiply real x inv-x)
          one))
        (equal
         (q7208500-r-multiply
          real x (q7208500-r-add real y z))
         (q7208500-r-add
          real
          (q7208500-r-multiply real x y)
          (q7208500-r-multiply real x z))))))))

(defun-sk q7208500-r-order-laws-p (real)
  (forall (x y z)
    (implies
     (and
      (q7208500-r-member-p real x)
      (q7208500-r-member-p real y)
      (q7208500-r-member-p real z))
     (let ((zero (q7208500-r-zero real)))
       (and
        (not (q7208500-r-less real x x))
        (or
         (equal x y)
         (q7208500-r-less real x y)
         (q7208500-r-less real y x))
        (implies
         (and
          (q7208500-r-less real x y)
          (q7208500-r-less real y z))
         (q7208500-r-less real x z))
        (implies
         (q7208500-r-less real x y)
         (q7208500-r-less
          real
          (q7208500-r-add real x z)
          (q7208500-r-add real y z)))
        (implies
         (and
          (q7208500-r-less real zero x)
          (q7208500-r-less real zero y))
         (q7208500-r-less
          real zero
          (q7208500-r-multiply real x y))))))))

(defun q7208500-r-singleton-set (real value)
  (list :q7208500-singleton real value))

(defun q7208500-r-set-member-p (real set value)
  (if
      (and
       (true-listp set)
       (equal (len set) 3)
       (equal (car set) :q7208500-singleton)
       (equal (cadr set) real))
      (equal value (caddr set))
    (q7208500-r-generic-set-member-p real set value)))

(defun-sk q7208500-r-valid-set-p (real set)
  (forall (x)
    (implies
     (q7208500-r-set-member-p real set x)
     (q7208500-r-member-p real x))))

(defun-sk q7208500-r-set-nonempty-p (real set)
  (exists (x)
    (and
     (q7208500-r-member-p real x)
     (q7208500-r-set-member-p real set x))))

(defun-sk q7208500-r-upper-bound-p (real set bound)
  (forall (x)
    (implies
     (and
      (q7208500-r-member-p real x)
      (q7208500-r-set-member-p real set x))
     (q7208500-r-leq real x bound))))

(defun-sk q7208500-r-bounded-above-p (real set)
  (exists (bound)
    (and
     (q7208500-r-member-p real bound)
     (q7208500-r-upper-bound-p real set bound))))

(defun-sk q7208500-r-least-upper-bound-p
    (real set supremum)
  (forall (bound)
    (and
     (q7208500-r-member-p real supremum)
     (q7208500-r-upper-bound-p real set supremum)
     (implies
      (and
       (q7208500-r-member-p real bound)
       (q7208500-r-upper-bound-p real set bound))
      (q7208500-r-leq real supremum bound)))))

(defun-sk q7208500-r-supremum-exists-p (real set)
  (exists (supremum)
    (q7208500-r-least-upper-bound-p
     real set supremum)))

(defun-sk q7208500-r-dedekind-complete-p (real)
  (forall (set)
    (implies
     (and
      (q7208500-r-valid-set-p real set)
      (q7208500-r-set-nonempty-p real set)
      (q7208500-r-bounded-above-p real set))
     (q7208500-r-supremum-exists-p real set))))

(defun q7208500-real-field-p (real)
  (let ((zero (q7208500-r-zero real))
        (one (q7208500-r-one real)))
    (and
     (q7208500-r-member-p real zero)
     (q7208500-r-member-p real one)
     (not (equal zero one))
     (q7208500-r-field-laws-p real)
     (q7208500-r-order-laws-p real)
     (q7208500-r-less real zero one)
     (q7208500-r-set-nonempty-p
      real (q7208500-r-singleton-set real zero))
     (q7208500-r-dedekind-complete-p real))))

;; Exact natural arithmetic interpreted in the real field.

(defun q7208500-natural-cast (real n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q7208500-r-zero real)
    (q7208500-r-add
     real
     (q7208500-natural-cast real (1- n))
     (q7208500-r-one real))))

(defun q7208500-natural-power (real value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (q7208500-r-one real)
    (q7208500-r-multiply
     real value
     (q7208500-natural-power
      real value (1- exponent)))))

(defun q7208500-natural-factorial-value (real n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q7208500-r-one real)
    (q7208500-r-multiply
     real
     (q7208500-natural-cast real n)
     (q7208500-natural-factorial-value real (1- n)))))

(defun q7208500-binomial-coefficient (n k)
  (declare (xargs :measure (nfix n)))
  (if (or (not (natp n))
          (not (natp k)))
      0
    (if (zp k)
        1
      (if (zp n)
          0
        (+ (q7208500-binomial-coefficient (1- n) k)
           (q7208500-binomial-coefficient
            (1- n) (1- k)))))))

;; The standard real exponential is the limit of sum_{j=0}^n x^j/j!.

(defun q7208500-exponential-partial-sum (real value n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q7208500-r-one real)
    (q7208500-r-add
     real
     (q7208500-exponential-partial-sum
      real value (1- n))
     (q7208500-r-divide
      real
      (q7208500-natural-power real value n)
      (q7208500-natural-factorial-value real n)))))

(defun-sk q7208500-exponential-tail-close-p
    (real argument value epsilon cutoff)
  (forall (n)
    (implies
     (and
      (natp n)
      (natp cutoff)
      (<= cutoff n))
     (q7208500-r-less
      real
      (q7208500-r-absolute-value
       real
       (q7208500-r-subtract
        real
        (q7208500-exponential-partial-sum
         real argument n)
        value))
      epsilon))))

(defun-sk q7208500-exponential-cutoff-exists-p
    (real argument value epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (q7208500-exponential-tail-close-p
      real argument value epsilon cutoff))))

(defun-sk q7208500-exponential-limit-p
    (real argument value)
  (forall (epsilon)
    (implies
     (q7208500-r-positive-p real epsilon)
     (q7208500-exponential-cutoff-exists-p
      real argument value epsilon))))

(defun-sk q7208500-standard-exponential-p (real)
  (forall (x)
    (implies
     (q7208500-r-member-p real x)
     (and
      (q7208500-r-positive-p
       real (q7208500-r-exponential real x))
      (q7208500-exponential-limit-p
       real x (q7208500-r-exponential real x))))))

;; Arbitrary real sequences and the source hypothesis n * p(n) -> r.

(defun-sk q7208500-sequence-typed-p (real sequence)
  (forall (n)
    (implies
     (natp n)
     (q7208500-r-member-p
      real (q7208500-sequence-value sequence n)))))

(defun q7208500-scaled-sequence-value
    (real sequence n)
  (q7208500-r-multiply
   real
   (q7208500-natural-cast real n)
   (q7208500-sequence-value sequence n)))

(defun-sk q7208500-scaled-tail-p
    (real sequence limit epsilon cutoff)
  (forall (n)
    (implies
     (and
      (natp n)
      (natp cutoff)
      (<= cutoff n))
     (q7208500-r-less
      real
      (q7208500-r-absolute-value
       real
       (q7208500-r-subtract
        real
        (q7208500-scaled-sequence-value
         real sequence n)
        limit))
      epsilon))))

(defun-sk q7208500-scaled-cutoff-exists-p
    (real sequence limit epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (q7208500-scaled-tail-p
      real sequence limit epsilon cutoff))))

(defun-sk q7208500-scaled-limit-p
    (real sequence limit)
  (forall (epsilon)
    (implies
     (q7208500-r-positive-p real epsilon)
     (q7208500-scaled-cutoff-exists-p
      real sequence limit epsilon))))

;; The exact binomial term
;; choose(n,k) * p(n)^k * (1-p(n))^(n-k), with truncated natural subtraction.

(defun q7208500-binomial-term
    (real sequence k n)
  (let* ((probability (q7208500-sequence-value sequence n))
         (one-minus-probability
          (q7208500-r-subtract
           real (q7208500-r-one real) probability))
         (choose-value
          (q7208500-natural-cast
           real (q7208500-binomial-coefficient n k)))
         (probability-power
          (q7208500-natural-power real probability k))
         (complement-power
          (q7208500-natural-power
           real
           one-minus-probability
           (nfix (- n k)))))
    (q7208500-r-multiply
     real
     (q7208500-r-multiply
      real choose-value probability-power)
     complement-power)))

(defun-sk q7208500-binomial-tail-p
    (real sequence k limit epsilon cutoff)
  (forall (n)
    (implies
     (and
      (natp n)
      (natp cutoff)
      (<= cutoff n))
     (q7208500-r-less
      real
      (q7208500-r-absolute-value
       real
       (q7208500-r-subtract
        real
        (q7208500-binomial-term
         real sequence k n)
        limit))
      epsilon))))

(defun-sk q7208500-binomial-cutoff-exists-p
    (real sequence k limit epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (q7208500-binomial-tail-p
      real sequence k limit epsilon cutoff))))

(defun-sk q7208500-binomial-limit-p
    (real sequence k limit)
  (forall (epsilon)
    (implies
     (q7208500-r-positive-p real epsilon)
     (q7208500-binomial-cutoff-exists-p
      real sequence k limit epsilon))))

(defun q7208500-poisson-limit-value (real r k)
  (q7208500-r-divide
   real
   (q7208500-r-multiply
    real
    (q7208500-r-exponential
     real (q7208500-r-negate real r))
    (q7208500-natural-power real r k))
   (q7208500-natural-factorial-value real k)))

(defun-sk thousand-theorems-q7208500-poisson-limit-theorem-statement ()
  (forall (real sequence r k)
    (implies
     (and
      (q7208500-real-field-p real)
      (q7208500-standard-exponential-p real)
      (natp k)
      (q7208500-r-member-p real r)
      (q7208500-sequence-typed-p real sequence)
      (q7208500-scaled-limit-p real sequence r))
     (q7208500-binomial-limit-p
      real
      sequence
      k
      (q7208500-poisson-limit-value real r k)))))

(value-triple :itpeval-statement-checked)
:q
