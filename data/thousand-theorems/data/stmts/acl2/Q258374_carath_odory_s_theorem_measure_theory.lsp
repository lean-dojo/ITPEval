;; Statement-only formalization of thousand-theorems corpus artifact Q258374,
;; "Carathéodory's theorem (measure theory)": for an outer measure, the sets
;; satisfying Carathéodory's splitting criterion form a measurable space.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))
(set-ignore-ok t)
(set-irrelevant-formals-ok t)

;; Function objects are represented by arbitrary tags interpreted through
;; conservative application interfaces.  Carrier predicates and every
;; algebraic, order, set, and outer-measure law are explicit below.

(defstub q258374-apply1 (function argument) t)
(defstub q258374-apply2 (function left right) t)

(defun q258374-member-p (carrier value)
  (if (q258374-apply1 carrier value) t nil))

;; A Dedekind-complete linearly ordered field presents the real numbers.

(defun-sk q258374-real-field-laws-p
    (carrier zero one add multiply negate inverse less)
  (forall (x y z)
    (implies
     (and
      (q258374-member-p carrier x)
      (q258374-member-p carrier y)
      (q258374-member-p carrier z))
     (let* ((xy-add (q258374-apply2 add x y))
            (yz-add (q258374-apply2 add y z))
            (xy-mul (q258374-apply2 multiply x y))
            (yz-mul (q258374-apply2 multiply y z))
            (neg-x (q258374-apply1 negate x))
            (inv-x (q258374-apply1 inverse x)))
       (and
        (q258374-member-p carrier xy-add)
        (q258374-member-p carrier xy-mul)
        (q258374-member-p carrier neg-x)
        (q258374-member-p carrier inv-x)
        (equal
         (q258374-apply2 add xy-add z)
         (q258374-apply2 add x yz-add))
        (equal xy-add (q258374-apply2 add y x))
        (equal (q258374-apply2 add x zero) x)
        (equal (q258374-apply2 add x neg-x) zero)
        (equal
         (q258374-apply2 multiply xy-mul z)
         (q258374-apply2 multiply x yz-mul))
        (equal xy-mul (q258374-apply2 multiply y x))
        (equal (q258374-apply2 multiply x one) x)
        (equal
         (q258374-apply2 multiply x yz-add)
         (q258374-apply2
          add
          (q258374-apply2 multiply x y)
          (q258374-apply2 multiply x z)))
        (implies
         (equal x zero)
         (equal inv-x zero))
        (implies
         (not (equal x zero))
         (equal (q258374-apply2 multiply x inv-x) one))
        (not (q258374-apply2 less x x))
        (or
         (equal x y)
         (q258374-apply2 less x y)
         (q258374-apply2 less y x))
        (implies
         (and
          (q258374-apply2 less x y)
          (q258374-apply2 less y z))
         (q258374-apply2 less x z))
        (implies
         (q258374-apply2 less x y)
         (q258374-apply2
          less
          (q258374-apply2 add x z)
          (q258374-apply2 add y z)))
        (implies
         (and
          (q258374-apply2 less zero x)
          (q258374-apply2 less zero y))
         (q258374-apply2
          less zero (q258374-apply2 multiply x y))))))))

(defun q258374-real-leq (less left right)
  (not (q258374-apply2 less right left)))

(defun-sk q258374-real-set-valid-p (carrier set)
  (forall (x)
    (implies
     (q258374-apply1 set x)
     (q258374-member-p carrier x))))

(defun-sk q258374-real-set-nonempty-p (carrier set)
  (exists (x)
    (and
     (q258374-member-p carrier x)
     (q258374-apply1 set x))))

(defun-sk q258374-real-upper-bound-p
    (carrier less set bound)
  (forall (x)
    (implies
     (and
      (q258374-member-p carrier x)
      (q258374-apply1 set x))
     (q258374-real-leq less x bound))))

(defun-sk q258374-real-bounded-above-p
    (carrier less set)
  (exists (bound)
    (and
     (q258374-member-p carrier bound)
     (q258374-real-upper-bound-p
      carrier less set bound))))

(defun-sk q258374-real-supremum-p
    (carrier less set supremum)
  (forall (bound)
    (and
     (q258374-member-p carrier supremum)
     (q258374-real-upper-bound-p
      carrier less set supremum)
     (implies
      (and
       (q258374-member-p carrier bound)
       (q258374-real-upper-bound-p
        carrier less set bound))
      (q258374-real-leq less supremum bound)))))

(defun-sk q258374-real-has-supremum-p
    (carrier less set)
  (exists (supremum)
    (q258374-real-supremum-p
     carrier less set supremum)))

(defun-sk q258374-real-complete-p (carrier less)
  (forall (set)
    (implies
     (and
      (q258374-real-set-valid-p carrier set)
      (q258374-real-set-nonempty-p carrier set)
      (q258374-real-bounded-above-p carrier less set))
     (q258374-real-has-supremum-p
      carrier less set))))

(defun q258374-real-p
    (carrier zero one add multiply negate inverse less)
  (and
   (q258374-member-p carrier zero)
   (q258374-member-p carrier one)
   (not (equal zero one))
   (q258374-apply2 less zero one)
   (q258374-real-field-laws-p
    carrier zero one add multiply negate inverse less)
   (q258374-real-complete-p carrier less)))

;; Extended nonnegative reals are represented canonically as a nonnegative
;; real value or a distinguished top element.

(defun q258374-ennreal-finite (value)
  (list :q258374-finite value))

(defun q258374-ennreal-top ()
  :q258374-top)

(defun q258374-ennreal-zero (real-zero)
  (q258374-ennreal-finite real-zero))

(defun q258374-ennreal-finite-p
    (real-carrier real-zero real-less value)
  (and
   (true-listp value)
   (equal (len value) 2)
   (equal (car value) :q258374-finite)
   (q258374-member-p real-carrier (cadr value))
   (q258374-real-leq real-less real-zero (cadr value))))

(defun q258374-ennreal-p
    (real-carrier real-zero real-less value)
  (or
   (equal value (q258374-ennreal-top))
   (q258374-ennreal-finite-p
    real-carrier real-zero real-less value)))

(defun q258374-ennreal-leq (real-less left right)
  (cond
   ((equal right (q258374-ennreal-top)) t)
   ((equal left (q258374-ennreal-top)) nil)
   (t
    (q258374-real-leq
     real-less (cadr left) (cadr right)))))

(defun q258374-ennreal-add (real-add left right)
  (if
      (or
       (equal left (q258374-ennreal-top))
       (equal right (q258374-ennreal-top)))
      (q258374-ennreal-top)
    (q258374-ennreal-finite
     (q258374-apply2 real-add (cadr left) (cadr right)))))

;; Arbitrary subsets of the point carrier and their standard operations.

(defun-sk q258374-set-p (point-carrier set)
  (forall (x)
    (implies
     (q258374-apply1 set x)
     (q258374-member-p point-carrier x))))

(defun-sk q258374-set-equivalent-p
    (point-carrier left right)
  (forall (x)
    (implies
     (q258374-member-p point-carrier x)
     (iff
      (q258374-apply1 left x)
      (q258374-apply1 right x)))))

(defun-sk q258374-subset-p
    (point-carrier left right)
  (forall (x)
    (implies
     (and
      (q258374-member-p point-carrier x)
      (q258374-apply1 left x))
     (q258374-apply1 right x))))

(defun-sk q258374-family-values-are-sets-p
    (point-carrier family)
  (forall (n)
    (implies
     (natp n)
     (q258374-set-p
      point-carrier (q258374-apply1 family n)))))

(defun-sk q258374-family-member-exists-p (family x)
  (exists (n)
    (and
     (natp n)
     (q258374-apply1
      (q258374-apply1 family n) x))))

(defun-sk q258374-set-operation-laws-p
    (point-carrier empty-set complement intersection difference union-family)
  (forall (left right family x)
    (and
     (q258374-set-p point-carrier empty-set)
     (implies
      (q258374-member-p point-carrier x)
      (not (q258374-apply1 empty-set x)))
     (implies
      (and
       (q258374-set-p point-carrier left)
       (q258374-set-p point-carrier right)
       (q258374-set-equivalent-p
        point-carrier left right))
      (equal left right))
     (implies
      (q258374-set-p point-carrier left)
      (and
       (q258374-set-p
        point-carrier
        (q258374-apply1 complement left))
       (implies
        (q258374-member-p point-carrier x)
        (iff
         (q258374-apply1
          (q258374-apply1 complement left) x)
         (not (q258374-apply1 left x))))))
     (implies
      (and
       (q258374-set-p point-carrier left)
       (q258374-set-p point-carrier right))
      (and
       (q258374-set-p
        point-carrier
        (q258374-apply2 intersection left right))
       (q258374-set-p
        point-carrier
        (q258374-apply2 difference left right))
       (implies
        (q258374-member-p point-carrier x)
        (and
         (iff
          (q258374-apply1
           (q258374-apply2 intersection left right) x)
          (and
           (q258374-apply1 left x)
           (q258374-apply1 right x)))
         (iff
          (q258374-apply1
           (q258374-apply2 difference left right) x)
          (and
           (q258374-apply1 left x)
           (not (q258374-apply1 right x))))))))
     (implies
      (q258374-family-values-are-sets-p
       point-carrier family)
      (and
       (q258374-set-p
        point-carrier
        (q258374-apply1 union-family family))
       (implies
        (q258374-member-p point-carrier x)
        (iff
         (q258374-apply1
          (q258374-apply1 union-family family) x)
         (q258374-family-member-exists-p family x))))))))

;; Infinite sums are least upper bounds of finite partial sums in ENNReal.

(defun q258374-measure-partial-sum
    (real-zero real-add measure family count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (q258374-ennreal-zero real-zero)
    (q258374-ennreal-add
     real-add
     (q258374-measure-partial-sum
      real-zero real-add measure family (1- count))
     (q258374-apply1
      measure (q258374-apply1 family (1- count))))))

(defun-sk q258374-measure-series-upper-bound-p
    (real-zero real-add real-less measure family bound)
  (forall (count)
    (implies
     (natp count)
     (q258374-ennreal-leq
      real-less
      (q258374-measure-partial-sum
       real-zero real-add measure family count)
      bound))))

(defun-sk q258374-measure-series-sum-p
    (real-carrier real-zero real-add real-less
     measure family total)
  (forall (bound)
    (and
     (q258374-ennreal-p
      real-carrier real-zero real-less total)
     (q258374-measure-series-upper-bound-p
      real-zero real-add real-less measure family total)
     (implies
      (and
       (q258374-ennreal-p
        real-carrier real-zero real-less bound)
       (q258374-measure-series-upper-bound-p
        real-zero real-add real-less measure family bound))
      (q258374-ennreal-leq real-less total bound)))))

;; The outer-measure predicate records exactly zero on the empty set,
;; monotonicity, extensionality, and countable subadditivity.

(defun-sk q258374-outer-measure-basic-laws-p
    (real-carrier real-zero real-less
     point-carrier empty-set measure)
  (forall (left right)
    (and
     (implies
      (q258374-set-p point-carrier left)
      (q258374-ennreal-p
       real-carrier real-zero real-less
       (q258374-apply1 measure left)))
     (implies
      (and
       (q258374-set-p point-carrier left)
       (q258374-set-p point-carrier right)
       (q258374-set-equivalent-p
        point-carrier left right))
      (equal
       (q258374-apply1 measure left)
       (q258374-apply1 measure right)))
     (equal
      (q258374-apply1 measure empty-set)
      (q258374-ennreal-zero real-zero))
     (implies
      (and
       (q258374-set-p point-carrier left)
       (q258374-set-p point-carrier right)
       (q258374-subset-p
        point-carrier left right))
      (q258374-ennreal-leq
       real-less
       (q258374-apply1 measure left)
       (q258374-apply1 measure right))))))

(defun-sk q258374-countable-subadditivity-instance-p
    (real-carrier real-zero real-add real-less
     measure family union)
  (exists (total)
    (and
     (q258374-measure-series-sum-p
      real-carrier real-zero real-add real-less
      measure family total)
     (q258374-ennreal-leq
      real-less
      (q258374-apply1 measure union)
      total))))

(defun-sk q258374-outer-measure-countable-laws-p
    (real-carrier real-zero real-add real-less
     point-carrier union-family measure)
  (forall (family)
    (implies
     (q258374-family-values-are-sets-p
      point-carrier family)
     (q258374-countable-subadditivity-instance-p
      real-carrier real-zero real-add real-less
      measure family
      (q258374-apply1 union-family family)))))

(defun q258374-outer-measure-p
    (real-carrier real-zero real-add real-less
     point-carrier empty-set union-family measure)
  (and
   (q258374-outer-measure-basic-laws-p
    real-carrier real-zero real-less
    point-carrier empty-set measure)
   (q258374-outer-measure-countable-laws-p
    real-carrier real-zero real-add real-less
    point-carrier union-family measure)))

;; Carathéodory measurability is the source criterion
;; m(t) = m(t intersection s) + m(t difference s), for every set t.

(defun-sk q258374-caratheodory-splitting-p
    (real-add point-carrier intersection difference measure set)
  (forall (test)
    (implies
     (q258374-set-p point-carrier test)
     (equal
      (q258374-apply1 measure test)
      (q258374-ennreal-add
       real-add
       (q258374-apply1
        measure (q258374-apply2 intersection test set))
       (q258374-apply1
        measure (q258374-apply2 difference test set)))))))

(defun q258374-caratheodory-measurable-set-p
    (real-add point-carrier intersection difference measure set)
  (and
   (q258374-set-p point-carrier set)
   (q258374-caratheodory-splitting-p
    real-add point-carrier intersection difference measure set)))

(defun-sk q258374-family-caratheodory-p
    (real-add point-carrier intersection difference measure family)
  (forall (n)
    (implies
     (natp n)
     (q258374-caratheodory-measurable-set-p
      real-add point-carrier intersection difference measure
      (q258374-apply1 family n)))))

(defun-sk q258374-caratheodory-extensional-p
    (real-add point-carrier intersection difference measure)
  (forall (left right)
    (implies
     (and
      (q258374-set-p point-carrier left)
      (q258374-set-p point-carrier right)
      (q258374-set-equivalent-p
       point-carrier left right))
     (iff
      (q258374-caratheodory-measurable-set-p
       real-add point-carrier intersection difference measure left)
      (q258374-caratheodory-measurable-set-p
       real-add point-carrier intersection difference measure right)))))

(defun-sk q258374-caratheodory-space-laws-p
    (real-add point-carrier complement intersection difference union-family
     measure)
  (forall (set family)
    (and
     (implies
      (q258374-caratheodory-measurable-set-p
       real-add point-carrier intersection difference measure set)
      (q258374-caratheodory-measurable-set-p
       real-add point-carrier intersection difference measure
       (q258374-apply1 complement set)))
     (implies
      (and
       (q258374-family-values-are-sets-p
        point-carrier family)
       (q258374-family-caratheodory-p
        real-add point-carrier intersection difference measure family))
      (q258374-caratheodory-measurable-set-p
       real-add point-carrier intersection difference measure
       (q258374-apply1 union-family family))))))

(defun q258374-caratheodory-measurable-space-p
    (real-add point-carrier empty-set complement intersection difference
     union-family measure)
  (and
   (q258374-caratheodory-extensional-p
    real-add point-carrier intersection difference measure)
   (q258374-caratheodory-measurable-set-p
    real-add point-carrier intersection difference measure empty-set)
   (q258374-caratheodory-space-laws-p
    real-add point-carrier complement intersection difference union-family
    measure)))

(defun-sk q258374-caratheodory-characterization-p
    (real-add point-carrier intersection difference measure)
  (forall (set)
    (implies
     (q258374-set-p point-carrier set)
     (iff
      (q258374-caratheodory-measurable-set-p
       real-add point-carrier intersection difference measure set)
      (q258374-caratheodory-splitting-p
       real-add point-carrier intersection difference measure set)))))

(defun-sk
    thousand-theorems-q258374-caratheodorys-theorem-measure-theory-statement
    ()
  (forall
    (real-carrier real-zero real-one real-add real-multiply real-negate
     real-inverse real-less point-carrier empty-set complement intersection
     difference union-family measure)
    (implies
     (and
      (q258374-real-p
       real-carrier real-zero real-one real-add real-multiply real-negate
       real-inverse real-less)
      (q258374-set-operation-laws-p
       point-carrier empty-set complement intersection difference
       union-family)
      (q258374-outer-measure-p
       real-carrier real-zero real-add real-less
       point-carrier empty-set union-family measure))
     (and
      (q258374-caratheodory-characterization-p
       real-add point-carrier intersection difference measure)
      (q258374-caratheodory-measurable-space-p
       real-add point-carrier empty-set complement intersection difference
       union-family measure)))))

(value-triple :itpeval-statement-checked)
:q
