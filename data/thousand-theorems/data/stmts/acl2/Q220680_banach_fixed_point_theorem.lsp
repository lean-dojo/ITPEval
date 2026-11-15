;; Statement-only formalization of thousand-theorems corpus artifact Q220680,
;; "Banach fixed-point theorem": a contraction on a complete extended metric
;; space has a fixed point approached by its iterates, with the stated
;; geometric extended-distance error bound. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Conservative application interfaces present arbitrary carriers, maps,
;; distances, subsets, and sequences. A Dedekind-complete ordered field
;; presents the real numbers. Its nonnegative cone with an adjoined top
;; element presents the extended nonnegative reals. All typing, field,
;; extended-metric, completeness, and contraction laws used by the source
;; theorem are explicit in the statement predicate.

(defstub q220680-apply1 (function x) t)
(defstub q220680-apply2 (function x y) t)

(defun q220680-member-p (carrier x)
  (if (q220680-apply1 carrier x) t nil))

;; A Dedekind-complete ordered-field presentation of the real numbers.

(defun-sk q220680-real-field-laws-p
    (carrier zero one add multiply negate inverse)
  (forall (x y z)
    (implies
     (and
      (q220680-member-p carrier x)
      (q220680-member-p carrier y)
      (q220680-member-p carrier z))
     (let* ((xy-add (q220680-apply2 add x y))
            (yz-add (q220680-apply2 add y z))
            (xy-multiply (q220680-apply2 multiply x y))
            (yz-multiply (q220680-apply2 multiply y z))
            (negative-x (q220680-apply1 negate x))
            (inverse-x (q220680-apply1 inverse x)))
       (and
        (q220680-member-p carrier xy-add)
        (q220680-member-p carrier xy-multiply)
        (q220680-member-p carrier negative-x)
        (q220680-member-p carrier inverse-x)
        (equal
         (q220680-apply2 add xy-add z)
         (q220680-apply2 add x yz-add))
        (equal xy-add (q220680-apply2 add y x))
        (equal (q220680-apply2 add x zero) x)
        (equal (q220680-apply2 add x negative-x) zero)
        (equal
         (q220680-apply2 multiply xy-multiply z)
         (q220680-apply2 multiply x yz-multiply))
        (equal xy-multiply (q220680-apply2 multiply y x))
        (equal (q220680-apply2 multiply x one) x)
        (equal (q220680-apply1 inverse zero) zero)
        (implies
         (not (equal x zero))
         (equal
          (q220680-apply2 multiply x inverse-x)
          one))
        (equal
         (q220680-apply2 multiply x yz-add)
         (q220680-apply2
          add
          (q220680-apply2 multiply x y)
          (q220680-apply2 multiply x z))))))))

(defun-sk q220680-real-order-laws-p
    (carrier zero add multiply less)
  (forall (x y z)
    (implies
     (and
      (q220680-member-p carrier x)
      (q220680-member-p carrier y)
      (q220680-member-p carrier z))
     (and
      (not (q220680-apply2 less x x))
      (or
       (equal x y)
       (q220680-apply2 less x y)
       (q220680-apply2 less y x))
      (implies
       (and
        (q220680-apply2 less x y)
        (q220680-apply2 less y z))
       (q220680-apply2 less x z))
      (implies
       (q220680-apply2 less x y)
       (q220680-apply2
        less
        (q220680-apply2 add x z)
        (q220680-apply2 add y z)))
      (implies
       (and
        (q220680-apply2 less zero x)
        (q220680-apply2 less zero y))
       (q220680-apply2
        less zero (q220680-apply2 multiply x y)))))))

(defun q220680-real-leq (less left right)
  (not (q220680-apply2 less right left)))

(defun q220680-real-subtract (add negate left right)
  (q220680-apply2
   add left (q220680-apply1 negate right)))

(defun-sk q220680-real-set-valid-p (carrier set)
  (forall (x)
    (implies
     (q220680-apply1 set x)
     (q220680-member-p carrier x))))

(defun-sk q220680-real-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (q220680-member-p carrier x)
     (q220680-apply1 set x))))

(defun-sk q220680-real-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and
      (q220680-member-p carrier x)
      (q220680-apply1 set x))
     (q220680-real-leq less x bound))))

(defun-sk q220680-real-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (q220680-member-p carrier bound)
     (q220680-real-upper-bound-p
      carrier less set bound))))

(defun-sk q220680-real-supremum-p
    (carrier less set supremum)
  (forall (bound)
    (and
     (q220680-member-p carrier supremum)
     (q220680-real-upper-bound-p
      carrier less set supremum)
     (implies
      (and
       (q220680-member-p carrier bound)
       (q220680-real-upper-bound-p
        carrier less set bound))
      (q220680-real-leq less supremum bound)))))

(defun-sk q220680-real-supremum-exists-p
    (carrier less set)
  (exists (supremum)
    (q220680-real-supremum-p
     carrier less set supremum)))

(defun-sk q220680-real-complete-p (carrier less)
  (forall (set)
    (implies
     (and
      (q220680-real-set-valid-p carrier set)
      (q220680-real-set-nonempty-p carrier set)
      (q220680-real-bounded-above-p carrier less set))
     (q220680-real-supremum-exists-p
      carrier less set))))

(defun q220680-real-field-p
    (carrier zero one add multiply negate inverse less)
  (and
   (q220680-member-p carrier zero)
   (q220680-member-p carrier one)
   (not (equal zero one))
   (q220680-real-field-laws-p
    carrier zero one add multiply negate inverse)
   (q220680-real-order-laws-p
    carrier zero add multiply less)
   (q220680-apply2 less zero one)
   (q220680-real-complete-p carrier less)))

;; Canonical extended nonnegative reals over the presented real field.

(defun q220680-ennreal-finite (value)
  (list :q220680-finite value))

(defun q220680-ennreal-top ()
  :q220680-top)

(defun q220680-ennreal-zero (real-zero)
  (q220680-ennreal-finite real-zero))

(defun q220680-ennreal-one (real-one)
  (q220680-ennreal-finite real-one))

(defun q220680-ennreal-finite-p
    (real-carrier real-zero real-less value)
  (and
   (true-listp value)
   (equal (len value) 2)
   (equal (car value) :q220680-finite)
   (q220680-member-p real-carrier (cadr value))
   (q220680-real-leq real-less real-zero (cadr value))))

(defun q220680-ennreal-p
    (real-carrier real-zero real-less value)
  (or
   (equal value (q220680-ennreal-top))
   (q220680-ennreal-finite-p
    real-carrier real-zero real-less value)))

(defun q220680-ennreal-leq (real-less left right)
  (cond
   ((equal right (q220680-ennreal-top)) t)
   ((equal left (q220680-ennreal-top)) nil)
   (t
    (q220680-real-leq
     real-less (cadr left) (cadr right)))))

(defun q220680-ennreal-less (real-less left right)
  (and
   (q220680-ennreal-leq real-less left right)
   (not (equal left right))))

(defun q220680-ennreal-add (real-add left right)
  (if (or
       (equal left (q220680-ennreal-top))
       (equal right (q220680-ennreal-top)))
      (q220680-ennreal-top)
    (q220680-ennreal-finite
     (q220680-apply2
      real-add (cadr left) (cadr right)))))

(defun q220680-ennreal-multiply
    (real-zero real-multiply left right)
  (cond
   ((or
     (equal left (q220680-ennreal-zero real-zero))
     (equal right (q220680-ennreal-zero real-zero)))
    (q220680-ennreal-zero real-zero))
   ((or
     (equal left (q220680-ennreal-top))
     (equal right (q220680-ennreal-top)))
    (q220680-ennreal-top))
   (t
    (q220680-ennreal-finite
     (q220680-apply2
      real-multiply (cadr left) (cadr right))))))

(defun q220680-ennreal-subtract
    (real-zero real-add real-negate real-less left right)
  (cond
   ((equal left (q220680-ennreal-top))
    (if (equal right (q220680-ennreal-top))
        (q220680-ennreal-zero real-zero)
      (q220680-ennreal-top)))
   ((equal right (q220680-ennreal-top))
    (q220680-ennreal-zero real-zero))
   ((q220680-apply2 real-less (cadr left) (cadr right))
    (q220680-ennreal-zero real-zero))
   (t
    (q220680-ennreal-finite
     (q220680-real-subtract
      real-add real-negate
      (cadr left) (cadr right))))))

(defun q220680-ennreal-inverse
    (real-zero real-inverse value)
  (cond
   ((equal value (q220680-ennreal-top))
    (q220680-ennreal-zero real-zero))
   ((equal value (q220680-ennreal-zero real-zero))
    (q220680-ennreal-top))
   (t
    (q220680-ennreal-finite
     (q220680-apply1 real-inverse (cadr value))))))

(defun q220680-ennreal-divide
    (real-zero real-multiply real-inverse numerator denominator)
  (q220680-ennreal-multiply
   real-zero real-multiply
   numerator
   (q220680-ennreal-inverse
    real-zero real-inverse denominator)))

(defun q220680-ennreal-power
    (real-zero real-one real-multiply base exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (q220680-ennreal-one real-one)
    (q220680-ennreal-multiply
     real-zero real-multiply
     base
     (q220680-ennreal-power
      real-zero real-one real-multiply
      base (1- exponent)))))

;; Extended metric spaces and sequential completeness.

(defun q220680-edistance (edistance x y)
  (q220680-apply2 edistance x y))

(defun-sk q220680-emetric-laws-p
    (real-carrier real-zero real-add real-less
     space-carrier edistance)
  (forall (x y z)
    (implies
     (and
      (q220680-member-p space-carrier x)
      (q220680-member-p space-carrier y)
      (q220680-member-p space-carrier z))
     (let ((dxy (q220680-edistance edistance x y))
           (dyz (q220680-edistance edistance y z))
           (dxz (q220680-edistance edistance x z)))
       (and
        (q220680-ennreal-p
         real-carrier real-zero real-less dxy)
        (q220680-ennreal-p
         real-carrier real-zero real-less dyz)
        (q220680-ennreal-p
         real-carrier real-zero real-less dxz)
        (equal
         (q220680-edistance edistance x x)
         (q220680-ennreal-zero real-zero))
        (equal dxy (q220680-edistance edistance y x))
        (iff
         (equal dxy (q220680-ennreal-zero real-zero))
         (equal x y))
        (q220680-ennreal-leq
         real-less
         dxz
         (q220680-ennreal-add
          real-add dxy dyz)))))))

(defun q220680-emetric-space-p
    (real-carrier real-zero real-add real-less
     space-carrier edistance)
  (q220680-emetric-laws-p
   real-carrier real-zero real-add real-less
   space-carrier edistance))

(defun-sk q220680-sequence-typed-p
    (space-carrier sequence)
  (forall (n)
    (implies
     (natp n)
     (q220680-member-p
      space-carrier
      (q220680-apply1 sequence n)))))

(defun-sk q220680-cauchy-tail-p
    (real-less edistance sequence epsilon cutoff)
  (forall (m n)
    (implies
     (and
      (natp m)
      (natp n)
      (natp cutoff)
      (<= cutoff m)
      (<= cutoff n))
     (q220680-ennreal-less
      real-less
      (q220680-edistance
       edistance
       (q220680-apply1 sequence m)
       (q220680-apply1 sequence n))
      (q220680-ennreal-finite epsilon)))))

(defun-sk q220680-cauchy-cutoff-exists-p
    (real-less edistance sequence epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (q220680-cauchy-tail-p
      real-less edistance sequence epsilon cutoff))))

(defun-sk q220680-cauchy-sequence-p
    (real-carrier real-zero real-less
     edistance sequence)
  (forall (epsilon)
    (implies
     (and
      (q220680-member-p real-carrier epsilon)
      (q220680-apply2 real-less real-zero epsilon))
     (q220680-cauchy-cutoff-exists-p
      real-less edistance sequence epsilon))))

(defun-sk q220680-convergence-tail-p
    (real-less edistance sequence limit epsilon cutoff)
  (forall (n)
    (implies
     (and
      (natp n)
      (natp cutoff)
      (<= cutoff n))
     (q220680-ennreal-less
      real-less
      (q220680-edistance
       edistance
       (q220680-apply1 sequence n)
       limit)
      (q220680-ennreal-finite epsilon)))))

(defun-sk q220680-convergence-cutoff-exists-p
    (real-less edistance sequence limit epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (q220680-convergence-tail-p
      real-less edistance sequence
      limit epsilon cutoff))))

(defun-sk q220680-sequence-converges-p
    (real-carrier real-zero real-less
     edistance sequence limit)
  (forall (epsilon)
    (implies
     (and
      (q220680-member-p real-carrier epsilon)
      (q220680-apply2 real-less real-zero epsilon))
     (q220680-convergence-cutoff-exists-p
      real-less edistance sequence limit epsilon))))

(defun-sk q220680-sequence-limit-exists-p
    (real-carrier real-zero real-less
     space-carrier edistance sequence)
  (exists (limit)
    (and
     (q220680-member-p space-carrier limit)
     (q220680-sequence-converges-p
      real-carrier real-zero real-less
      edistance sequence limit))))

(defun-sk q220680-complete-space-p
    (real-carrier real-zero real-less
     space-carrier edistance)
  (forall (sequence)
    (implies
     (and
      (q220680-sequence-typed-p
       space-carrier sequence)
      (q220680-cauchy-sequence-p
       real-carrier real-zero real-less
       edistance sequence))
     (q220680-sequence-limit-exists-p
      real-carrier real-zero real-less
      space-carrier edistance sequence))))

;; Contracting maps and their iterates.

(defun-sk q220680-map-typed-p (space-carrier map)
  (forall (x)
    (implies
     (q220680-member-p space-carrier x)
     (q220680-member-p
      space-carrier
      (q220680-apply1 map x)))))

(defun-sk q220680-lipschitz-with-p
    (real-zero real-multiply real-less
     space-carrier edistance map k)
  (forall (x y)
    (implies
     (and
      (q220680-member-p space-carrier x)
      (q220680-member-p space-carrier y))
     (q220680-ennreal-leq
      real-less
      (q220680-edistance
       edistance
       (q220680-apply1 map x)
       (q220680-apply1 map y))
      (q220680-ennreal-multiply
       real-zero real-multiply
       (q220680-ennreal-finite k)
       (q220680-edistance edistance x y))))))

(defun q220680-contracting-with-p
    (real-carrier real-zero real-one real-multiply real-less
     space-carrier edistance map k)
  (and
   (q220680-member-p real-carrier k)
   (q220680-real-leq real-less real-zero k)
   (q220680-apply2 real-less k real-one)
   (q220680-map-typed-p space-carrier map)
   (q220680-lipschitz-with-p
    real-zero real-multiply real-less
    space-carrier edistance map k)))

(defun q220680-iterate (map n x)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      x
    (q220680-apply1
     map
     (q220680-iterate map (1- n) x))))

(defun-sk q220680-orbit-convergence-tail-p
    (real-less edistance map start limit epsilon cutoff)
  (forall (n)
    (implies
     (and
      (natp n)
      (natp cutoff)
      (<= cutoff n))
     (q220680-ennreal-less
      real-less
      (q220680-edistance
       edistance
       (q220680-iterate map n start)
       limit)
      (q220680-ennreal-finite epsilon)))))

(defun-sk q220680-orbit-convergence-cutoff-exists-p
    (real-less edistance map start limit epsilon)
  (exists (cutoff)
    (and
     (natp cutoff)
     (q220680-orbit-convergence-tail-p
      real-less edistance map start limit
      epsilon cutoff))))

(defun-sk q220680-orbit-converges-p
    (real-carrier real-zero real-less
     edistance map start limit)
  (forall (epsilon)
    (implies
     (and
      (q220680-member-p real-carrier epsilon)
      (q220680-apply2 real-less real-zero epsilon))
     (q220680-orbit-convergence-cutoff-exists-p
      real-less edistance map start limit epsilon))))

(defun q220680-geometric-bound
    (real-zero real-one real-add real-multiply
     real-negate real-inverse real-less
     edistance map k start n)
  (let* ((initial-distance
          (q220680-edistance
           edistance start (q220680-apply1 map start)))
         (coefficient
          (q220680-ennreal-finite k))
         (coefficient-power
          (q220680-ennreal-power
           real-zero real-one real-multiply
           coefficient n))
         (denominator
          (q220680-ennreal-subtract
           real-zero real-add real-negate real-less
           (q220680-ennreal-one real-one)
           coefficient)))
    (q220680-ennreal-divide
     real-zero real-multiply real-inverse
     (q220680-ennreal-multiply
      real-zero real-multiply
      initial-distance coefficient-power)
     denominator)))

(defun-sk q220680-geometric-error-bound-p
    (real-zero real-one real-add real-multiply
     real-negate real-inverse real-less
     edistance map k start limit)
  (forall (n)
    (implies
     (natp n)
     (q220680-ennreal-leq
      real-less
      (q220680-edistance
       edistance
       (q220680-iterate map n start)
       limit)
      (q220680-geometric-bound
       real-zero real-one real-add real-multiply
       real-negate real-inverse real-less
       edistance map k start n)))))

(defun q220680-fixed-point-conclusion-p
    (real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less
     space-carrier edistance map k start fixed-point)
  (and
   (q220680-member-p space-carrier fixed-point)
   (equal
    (q220680-apply1 map fixed-point)
    fixed-point)
   (q220680-orbit-converges-p
    real-carrier real-zero real-less
    edistance map start fixed-point)
   (q220680-geometric-error-bound-p
    real-zero real-one real-add real-multiply
    real-negate real-inverse real-less
    edistance map k start fixed-point)))

(defun-sk q220680-fixed-point-exists-p
    (real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less
     space-carrier edistance map k start)
  (exists (fixed-point)
    (q220680-fixed-point-conclusion-p
     real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less
     space-carrier edistance map k start fixed-point)))

(defun thousand-theorems-q220680-banach-fixed-point-theorem-statement
    (real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less
     space-carrier edistance map k start)
  (implies
   (and
    (q220680-real-field-p
     real-carrier real-zero real-one real-add real-multiply
     real-negate real-inverse real-less)
    (q220680-emetric-space-p
     real-carrier real-zero real-add real-less
     space-carrier edistance)
    (q220680-complete-space-p
     real-carrier real-zero real-less
     space-carrier edistance)
    (q220680-contracting-with-p
     real-carrier real-zero real-one real-multiply real-less
     space-carrier edistance map k)
    (q220680-member-p space-carrier start)
    (not
     (equal
      (q220680-edistance
       edistance start (q220680-apply1 map start))
      (q220680-ennreal-top))))
   (q220680-fixed-point-exists-p
    real-carrier real-zero real-one real-add real-multiply
    real-negate real-inverse real-less
    space-carrier edistance map k start)))

(value-triple :itpeval-statement-checked)
:q
