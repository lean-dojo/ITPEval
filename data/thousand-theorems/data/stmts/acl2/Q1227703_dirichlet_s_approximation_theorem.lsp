;; Statement-only formalization of thousand-theorems corpus artifact Q1227703,
;; "Dirichlet's approximation theorem": every point of the real additive
;; circle of positive circumference T has a multiple j, with 1 <= j <= n,
;; whose circle norm is at most T/(n+1). This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The real numbers are presented as an arbitrary Dedekind-complete ordered
;; field. Tame unary function objects represent arbitrary subsets for the
;; completeness law. This avoids restricting the source's real domain to the
;; rational numbers available as executable ACL2 numbers.

(defstub q1227703-real-p (x) t)
(defstub q1227703-zero () t)
(defstub q1227703-one () t)
(defstub q1227703-add (left right) t)
(defstub q1227703-multiply (left right) t)
(defstub q1227703-negate (x) t)
(defstub q1227703-inverse (x) t)
(defstub q1227703-less (left right) t)
(defstub q1227703-supremum (set) t)

(defun q1227703-leq (left right)
  (not (q1227703-less right left)))

(defun q1227703-subtract (left right)
  (q1227703-add left (q1227703-negate right)))

(defun q1227703-absolute-value (x)
  (if (q1227703-less x (q1227703-zero))
      (q1227703-negate x)
    x))

(defun q1227703-positive-p (x)
  (and
   (q1227703-real-p x)
   (q1227703-less (q1227703-zero) x)))

(defun q1227703-set-member-p (set x)
  (if (apply$ set (list x)) t nil))

(defun-sk q1227703-field-laws-p ()
  (forall (x y z)
    (implies
     (and
      (q1227703-real-p x)
      (q1227703-real-p y)
      (q1227703-real-p z))
     (let* ((zero (q1227703-zero))
            (one (q1227703-one))
            (xy-add (q1227703-add x y))
            (yz-add (q1227703-add y z))
            (xy-mul (q1227703-multiply x y))
            (yz-mul (q1227703-multiply y z))
            (neg-x (q1227703-negate x))
            (inv-x (q1227703-inverse x)))
       (and
        (q1227703-real-p xy-add)
        (q1227703-real-p xy-mul)
        (q1227703-real-p neg-x)
        (q1227703-real-p inv-x)
        (equal
         (q1227703-add xy-add z)
         (q1227703-add x yz-add))
        (equal xy-add (q1227703-add y x))
        (equal (q1227703-add x zero) x)
        (equal (q1227703-add x neg-x) zero)
        (equal
         (q1227703-multiply xy-mul z)
         (q1227703-multiply x yz-mul))
        (equal xy-mul (q1227703-multiply y x))
        (equal (q1227703-multiply x one) x)
        (implies
         (equal x zero)
         (equal inv-x zero))
        (implies
         (not (equal x zero))
         (equal (q1227703-multiply x inv-x) one))
        (equal
         (q1227703-multiply x yz-add)
         (q1227703-add
          (q1227703-multiply x y)
          (q1227703-multiply x z))))))))

(defun-sk q1227703-order-laws-p ()
  (forall (x y z)
    (implies
     (and
      (q1227703-real-p x)
      (q1227703-real-p y)
      (q1227703-real-p z))
     (let ((zero (q1227703-zero)))
       (and
        (not (q1227703-less x x))
        (or
         (equal x y)
         (q1227703-less x y)
         (q1227703-less y x))
        (implies
         (and
          (q1227703-less x y)
          (q1227703-less y z))
         (q1227703-less x z))
        (implies
         (q1227703-less x y)
         (q1227703-less
          (q1227703-add x z)
          (q1227703-add y z)))
        (implies
         (and
          (q1227703-less zero x)
          (q1227703-less zero y))
         (q1227703-less
          zero
          (q1227703-multiply x y))))))))

(defun-sk q1227703-valid-real-set-p (set)
  (forall (x)
    (implies
     (q1227703-set-member-p set x)
     (q1227703-real-p x))))

(defun-sk q1227703-set-nonempty-p (set)
  (exists (x)
    (and
     (q1227703-real-p x)
     (q1227703-set-member-p set x))))

(defun-sk q1227703-upper-bound-p (set bound)
  (forall (x)
    (implies
     (and
      (q1227703-real-p x)
      (q1227703-set-member-p set x))
     (q1227703-leq x bound))))

(defun-sk q1227703-bounded-above-p (set)
  (exists (bound)
    (and
     (q1227703-real-p bound)
     (q1227703-upper-bound-p set bound))))

(defun-sk q1227703-least-upper-bound-p (set supremum)
  (forall (bound)
    (and
     (q1227703-real-p supremum)
     (q1227703-upper-bound-p set supremum)
     (implies
      (and
       (q1227703-real-p bound)
       (q1227703-upper-bound-p set bound))
      (q1227703-leq supremum bound)))))

(defun-sk q1227703-dedekind-complete-p ()
  (forall (set)
    (implies
     (and
      (tamep-functionp set)
      (q1227703-valid-real-set-p set)
      (q1227703-set-nonempty-p set)
      (q1227703-bounded-above-p set))
     (q1227703-least-upper-bound-p
      set
      (q1227703-supremum set)))))

(defun q1227703-real-context-p ()
  (let ((zero (q1227703-zero))
        (one (q1227703-one)))
    (and
     (q1227703-real-p zero)
     (q1227703-real-p one)
     (not (equal zero one))
     (q1227703-field-laws-p)
     (q1227703-order-laws-p)
     (q1227703-less zero one)
     (q1227703-dedekind-complete-p))))

;; Natural and integer scalar multiplication are the canonical repeated
;; additions in the presented real field.

(defun q1227703-nsmul (n x)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (q1227703-zero)
    (q1227703-add
     x
     (q1227703-nsmul (- n 1) x))))

(defun q1227703-zsmul (k x)
  (if (and (integerp k) (< k 0))
      (q1227703-negate
       (q1227703-nsmul (- k) x))
    (q1227703-nsmul (nfix k) x)))

(defun q1227703-natural-cast (n)
  (q1227703-nsmul n (q1227703-one)))

(defun q1227703-divide (numerator denominator)
  (q1227703-multiply
   numerator
   (q1227703-inverse denominator)))

;; A representative X denotes a point of R/(T Z). The quotient norm inequality
;; ||j [X]|| <= B is definitionally eliminated as the existence of an integer
;; K with |j X - K T| <= B. Changing X by an integer multiple of T only changes
;; K, so this is independent of the chosen representative.

(defun-sk q1227703-integer-approximation-p
    (period representative j bound)
  (exists (k)
    (and
     (integerp k)
     (q1227703-leq
      (q1227703-absolute-value
       (q1227703-subtract
        (q1227703-nsmul j representative)
        (q1227703-zsmul k period)))
      bound))))

(defun-sk q1227703-dirichlet-witness-p
    (period representative n)
  (exists (j)
    (and
     (natp j)
     (<= 1 j)
     (<= j n)
     (q1227703-integer-approximation-p
      period
      representative
      j
      (q1227703-divide
       period
       (q1227703-natural-cast (+ n 1)))))))

(defun-sk thousand-theorems-q1227703-dirichlet-approximation-statement ()
  (forall (period representative n)
    (implies
     (and
      (q1227703-real-context-p)
      (q1227703-positive-p period)
      (q1227703-real-p representative)
      (natp n)
      (< 0 n))
     (q1227703-dirichlet-witness-p
      period representative n))))

(value-triple :itpeval-statement-checked)
:q
