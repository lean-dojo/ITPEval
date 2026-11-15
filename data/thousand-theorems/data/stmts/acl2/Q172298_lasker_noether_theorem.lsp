;; Statement-only formalization of thousand-theorems corpus artifact Q172298,
;; "Lasker–Noether theorem": a finite primary decomposition of a submodule can
;; be replaced by one whose colon-ideal radicals are pairwise distinct. This
;; file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Tame function objects represent the arbitrary semiring and module carriers,
;; their operations, and arbitrary submodule membership predicates. Finite
;; lists represent Finsets, with extensional equality used for submodules.

(defun q172298-member-p (predicate value)
  (if (apply$ predicate (list value))
      t
    nil))

(defun q172298-binary-value (operation left right)
  (apply$ operation (list left right)))

(defun q172298-ring-add (addition left right)
  (q172298-binary-value addition left right))

(defun q172298-ring-mul (multiplication left right)
  (q172298-binary-value multiplication left right))

(defun q172298-module-add (addition left right)
  (q172298-binary-value addition left right))

(defun q172298-smul (scalar-action scalar vector)
  (q172298-binary-value scalar-action scalar vector))

(defun-sk q172298-commutative-semiring-laws-p
    (ring-carrier ring-zero ring-one ring-addition ring-multiplication)
  (forall (x y z)
    (and
     (implies
      (q172298-member-p ring-carrier x)
      (and
       (equal
        (q172298-ring-add ring-addition x ring-zero)
        x)
       (equal
        (q172298-ring-add ring-addition ring-zero x)
        x)
       (equal
        (q172298-ring-mul ring-multiplication x ring-one)
        x)
       (equal
        (q172298-ring-mul ring-multiplication ring-one x)
        x)
       (equal
        (q172298-ring-mul ring-multiplication x ring-zero)
        ring-zero)
       (equal
        (q172298-ring-mul ring-multiplication ring-zero x)
        ring-zero)))
     (implies
      (and
       (q172298-member-p ring-carrier x)
       (q172298-member-p ring-carrier y))
      (and
       (q172298-member-p
        ring-carrier
        (q172298-ring-add ring-addition x y))
       (q172298-member-p
        ring-carrier
        (q172298-ring-mul ring-multiplication x y))
       (equal
        (q172298-ring-add ring-addition x y)
        (q172298-ring-add ring-addition y x))
       (equal
        (q172298-ring-mul ring-multiplication x y)
        (q172298-ring-mul ring-multiplication y x))))
     (implies
      (and
       (q172298-member-p ring-carrier x)
       (q172298-member-p ring-carrier y)
       (q172298-member-p ring-carrier z))
      (and
       (equal
        (q172298-ring-add
         ring-addition
         (q172298-ring-add ring-addition x y)
         z)
        (q172298-ring-add
         ring-addition
         x
         (q172298-ring-add ring-addition y z)))
       (equal
        (q172298-ring-mul
         ring-multiplication
         (q172298-ring-mul ring-multiplication x y)
         z)
        (q172298-ring-mul
         ring-multiplication
         x
         (q172298-ring-mul ring-multiplication y z)))
       (equal
        (q172298-ring-mul
         ring-multiplication
         x
         (q172298-ring-add ring-addition y z))
        (q172298-ring-add
         ring-addition
         (q172298-ring-mul ring-multiplication x y)
         (q172298-ring-mul ring-multiplication x z)))
       (equal
        (q172298-ring-mul
         ring-multiplication
         (q172298-ring-add ring-addition x y)
         z)
        (q172298-ring-add
         ring-addition
         (q172298-ring-mul ring-multiplication x z)
         (q172298-ring-mul ring-multiplication y z))))))))

(defun q172298-commutative-semiring-p
    (ring-carrier ring-zero ring-one ring-addition ring-multiplication)
  (and
   (tamep-functionp ring-carrier)
   (tamep-functionp ring-addition)
   (tamep-functionp ring-multiplication)
   (q172298-member-p ring-carrier ring-zero)
   (q172298-member-p ring-carrier ring-one)
   (q172298-commutative-semiring-laws-p
    ring-carrier
    ring-zero
    ring-one
    ring-addition
    ring-multiplication)))

(defun-sk q172298-module-laws-p
    (ring-carrier
     ring-zero
     ring-one
     ring-addition
     ring-multiplication
     module-carrier
     module-zero
     module-addition
     scalar-action)
  (forall (a b x y z)
    (and
     (implies
      (q172298-member-p module-carrier x)
      (and
       (equal
        (q172298-module-add module-addition x module-zero)
        x)
       (equal
        (q172298-module-add module-addition module-zero x)
        x)
       (equal
        (q172298-smul scalar-action ring-one x)
        x)
       (equal
        (q172298-smul scalar-action ring-zero x)
        module-zero)))
     (implies
      (and
       (q172298-member-p module-carrier x)
       (q172298-member-p module-carrier y))
      (and
       (q172298-member-p
        module-carrier
        (q172298-module-add module-addition x y))
       (equal
        (q172298-module-add module-addition x y)
        (q172298-module-add module-addition y x))))
     (implies
      (and
       (q172298-member-p module-carrier x)
       (q172298-member-p module-carrier y)
       (q172298-member-p module-carrier z))
      (equal
       (q172298-module-add
        module-addition
        (q172298-module-add module-addition x y)
        z)
       (q172298-module-add
        module-addition
        x
        (q172298-module-add module-addition y z))))
     (implies
      (and
       (q172298-member-p ring-carrier a)
       (q172298-member-p module-carrier x))
      (and
       (q172298-member-p
        module-carrier
        (q172298-smul scalar-action a x))
       (equal
        (q172298-smul scalar-action a module-zero)
        module-zero)))
     (implies
      (and
       (q172298-member-p ring-carrier a)
       (q172298-member-p module-carrier x)
       (q172298-member-p module-carrier y))
      (equal
       (q172298-smul
        scalar-action
        a
        (q172298-module-add module-addition x y))
       (q172298-module-add
        module-addition
        (q172298-smul scalar-action a x)
        (q172298-smul scalar-action a y))))
     (implies
      (and
       (q172298-member-p ring-carrier a)
       (q172298-member-p ring-carrier b)
       (q172298-member-p module-carrier x))
      (and
       (equal
        (q172298-smul
         scalar-action
         (q172298-ring-add ring-addition a b)
         x)
        (q172298-module-add
         module-addition
         (q172298-smul scalar-action a x)
         (q172298-smul scalar-action b x)))
       (equal
        (q172298-smul
         scalar-action
         (q172298-ring-mul ring-multiplication a b)
         x)
        (q172298-smul
         scalar-action
         a
         (q172298-smul scalar-action b x))))))))

(defun q172298-module-p
    (ring-carrier
     ring-zero
     ring-one
     ring-addition
     ring-multiplication
     module-carrier
     module-zero
     module-addition
     scalar-action)
  (and
   (tamep-functionp module-carrier)
   (tamep-functionp module-addition)
   (tamep-functionp scalar-action)
   (q172298-member-p module-carrier module-zero)
   (q172298-module-laws-p
    ring-carrier
    ring-zero
    ring-one
    ring-addition
    ring-multiplication
    module-carrier
    module-zero
    module-addition
    scalar-action)))

(defun-sk q172298-submodule-laws-p
    (ring-carrier
     module-carrier
     module-zero
     module-addition
     scalar-action
     submodule)
  (forall (a x y)
    (and
     (implies
      (q172298-member-p submodule x)
      (q172298-member-p module-carrier x))
     (implies
      (and
       (q172298-member-p submodule x)
       (q172298-member-p submodule y))
      (q172298-member-p
       submodule
       (q172298-module-add module-addition x y)))
     (implies
      (and
       (q172298-member-p ring-carrier a)
       (q172298-member-p submodule x))
      (q172298-member-p
       submodule
       (q172298-smul scalar-action a x))))))

(defun q172298-submodule-p
    (ring-carrier
     module-carrier
     module-zero
     module-addition
     scalar-action
     submodule)
  (and
   (tamep-functionp submodule)
   (q172298-member-p submodule module-zero)
   (q172298-submodule-laws-p
    ring-carrier
    module-carrier
    module-zero
    module-addition
    scalar-action
    submodule)))

(defun-sk q172298-same-submodule-p (left right)
  (forall (x)
    (iff
     (q172298-member-p left x)
     (q172298-member-p right x))))

(defun q172298-not-same-as-any-p (submodule family)
  (if (consp family)
      (and
       (not
        (q172298-same-submodule-p submodule (car family)))
       (q172298-not-same-as-any-p submodule (cdr family)))
    (equal family nil)))

(defun q172298-extensionally-nodup-p (family)
  (if (consp family)
      (and
       (q172298-not-same-as-any-p (car family) (cdr family))
       (q172298-extensionally-nodup-p (cdr family)))
    (equal family nil)))

(defun q172298-all-submodules-p
    (ring-carrier
     module-carrier
     module-zero
     module-addition
     scalar-action
     family)
  (if (consp family)
      (and
       (q172298-submodule-p
        ring-carrier
        module-carrier
        module-zero
        module-addition
        scalar-action
        (car family))
       (q172298-all-submodules-p
        ring-carrier
        module-carrier
        module-zero
        module-addition
        scalar-action
        (cdr family)))
    (equal family nil)))

(defun q172298-finite-submodules-p
    (ring-carrier
     module-carrier
     module-zero
     module-addition
     scalar-action
     family)
  (and
   (true-listp family)
   (q172298-all-submodules-p
    ring-carrier
    module-carrier
    module-zero
    module-addition
    scalar-action
    family)
   (q172298-extensionally-nodup-p family)))

(defun q172298-member-of-every-submodule-p (family value)
  (if (consp family)
      (and
       (q172298-member-p (car family) value)
       (q172298-member-of-every-submodule-p (cdr family) value))
    (equal family nil)))

(defun-sk q172298-infimum-equals-p
    (module-carrier submodule family)
  (forall (x)
    (iff
     (q172298-member-p submodule x)
     (and
      (q172298-member-p module-carrier x)
      (q172298-member-of-every-submodule-p family x)))))

(defun q172298-ring-power
    (ring-one ring-multiplication base exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      ring-one
    (q172298-ring-mul
     ring-multiplication
     base
     (q172298-ring-power
      ring-one
      ring-multiplication
      base
      (1- exponent)))))

(defun-sk q172298-annihilates-quotient-p
    (module-carrier scalar-action submodule scalar)
  (forall (x)
    (implies
     (q172298-member-p module-carrier x)
     (q172298-member-p
      submodule
      (q172298-smul scalar-action scalar x)))))

(defun-sk q172298-colon-radical-member-p
    (ring-carrier
     ring-one
     ring-multiplication
     module-carrier
     scalar-action
     submodule
     scalar)
  (exists (exponent)
    (and
     (q172298-member-p ring-carrier scalar)
     (natp exponent)
     (q172298-annihilates-quotient-p
      module-carrier
      scalar-action
      submodule
      (q172298-ring-power
       ring-one
       ring-multiplication
       scalar
       exponent)))))

(defun-sk q172298-proper-submodule-p (module-carrier submodule)
  (exists (x)
    (and
     (q172298-member-p module-carrier x)
     (not (q172298-member-p submodule x)))))

(defun-sk q172298-primary-law-p
    (ring-carrier
     ring-one
     ring-multiplication
     module-carrier
     scalar-action
     submodule)
  (forall (scalar x)
    (implies
     (and
      (q172298-member-p ring-carrier scalar)
      (q172298-member-p module-carrier x)
      (q172298-member-p
       submodule
       (q172298-smul scalar-action scalar x)))
     (or
      (q172298-member-p submodule x)
      (q172298-colon-radical-member-p
       ring-carrier
       ring-one
       ring-multiplication
       module-carrier
       scalar-action
       submodule
       scalar)))))

(defun q172298-primary-submodule-p
    (ring-carrier
     ring-one
     ring-multiplication
     module-carrier
     module-zero
     module-addition
     scalar-action
     submodule)
  (and
   (q172298-submodule-p
    ring-carrier
    module-carrier
    module-zero
    module-addition
    scalar-action
    submodule)
   (q172298-proper-submodule-p module-carrier submodule)
   (q172298-primary-law-p
    ring-carrier
    ring-one
    ring-multiplication
    module-carrier
    scalar-action
    submodule)))

(defun q172298-all-primary-p
    (ring-carrier
     ring-one
     ring-multiplication
     module-carrier
     module-zero
     module-addition
     scalar-action
     family)
  (if (consp family)
      (and
       (q172298-primary-submodule-p
        ring-carrier
        ring-one
        ring-multiplication
        module-carrier
        module-zero
        module-addition
        scalar-action
        (car family))
       (q172298-all-primary-p
        ring-carrier
        ring-one
        ring-multiplication
        module-carrier
        module-zero
        module-addition
        scalar-action
        (cdr family)))
    (equal family nil)))

(defun-sk q172298-colon-radicals-equal-p
    (ring-carrier
     ring-one
     ring-multiplication
     module-carrier
     scalar-action
     left
     right)
  (forall (scalar)
    (iff
     (q172298-colon-radical-member-p
      ring-carrier
      ring-one
      ring-multiplication
      module-carrier
      scalar-action
      left
      scalar)
     (q172298-colon-radical-member-p
      ring-carrier
      ring-one
      ring-multiplication
      module-carrier
      scalar-action
      right
      scalar))))

(defun q172298-radical-distinct-from-family-p
    (ring-carrier
     ring-one
     ring-multiplication
     module-carrier
     scalar-action
     submodule
     family)
  (if (consp family)
      (and
       (not
        (q172298-colon-radicals-equal-p
         ring-carrier
         ring-one
         ring-multiplication
         module-carrier
         scalar-action
         submodule
         (car family)))
       (q172298-radical-distinct-from-family-p
        ring-carrier
        ring-one
        ring-multiplication
        module-carrier
        scalar-action
        submodule
        (cdr family)))
    (equal family nil)))

(defun q172298-pairwise-distinct-colon-radicals-p
    (ring-carrier
     ring-one
     ring-multiplication
     module-carrier
     scalar-action
     family)
  (if (consp family)
      (and
       (q172298-radical-distinct-from-family-p
        ring-carrier
        ring-one
        ring-multiplication
        module-carrier
        scalar-action
        (car family)
        (cdr family))
       (q172298-pairwise-distinct-colon-radicals-p
        ring-carrier
        ring-one
        ring-multiplication
        module-carrier
        scalar-action
        (cdr family)))
    (equal family nil)))

(defun-sk q172298-refined-decomposition-exists-p
    (ring-carrier
     ring-one
     ring-multiplication
     module-carrier
     module-zero
     module-addition
     scalar-action
     submodule)
  (exists (family)
    (and
     (q172298-finite-submodules-p
      ring-carrier
      module-carrier
      module-zero
      module-addition
      scalar-action
      family)
     (q172298-infimum-equals-p
      module-carrier
      submodule
      family)
     (q172298-all-primary-p
      ring-carrier
      ring-one
      ring-multiplication
      module-carrier
      module-zero
      module-addition
      scalar-action
      family)
     (q172298-pairwise-distinct-colon-radicals-p
      ring-carrier
      ring-one
      ring-multiplication
      module-carrier
      scalar-action
      family))))

(defun-sk
    thousand-theorems-q172298-lasker-noether-theorem-statement ()
  (forall
   (ring-carrier
    ring-zero
    ring-one
    ring-addition
    ring-multiplication
    module-carrier
    module-zero
    module-addition
    scalar-action
    submodule
    family)
   (implies
    (and
     (q172298-commutative-semiring-p
      ring-carrier
      ring-zero
      ring-one
      ring-addition
      ring-multiplication)
     (q172298-module-p
      ring-carrier
      ring-zero
      ring-one
      ring-addition
      ring-multiplication
      module-carrier
      module-zero
      module-addition
      scalar-action)
     (q172298-submodule-p
      ring-carrier
      module-carrier
      module-zero
      module-addition
      scalar-action
      submodule)
     (q172298-finite-submodules-p
      ring-carrier
      module-carrier
      module-zero
      module-addition
      scalar-action
      family)
     (q172298-infimum-equals-p
      module-carrier
      submodule
      family)
     (q172298-all-primary-p
      ring-carrier
      ring-one
      ring-multiplication
      module-carrier
      module-zero
      module-addition
      scalar-action
      family))
    (q172298-refined-decomposition-exists-p
     ring-carrier
     ring-one
     ring-multiplication
     module-carrier
     module-zero
     module-addition
     scalar-action
     submodule))))

(value-triple :itpeval-statement-checked)
:q
