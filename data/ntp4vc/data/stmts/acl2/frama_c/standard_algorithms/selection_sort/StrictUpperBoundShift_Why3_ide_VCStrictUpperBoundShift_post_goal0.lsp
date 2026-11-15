;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/selection_sort/StrictUpperBoundShift_Why3_ide_VCStrictUpperBoundShift_post_goal0:
;; shifting an array base to the lower endpoint of a strict-upper-bound
;; interval preserves the corresponding strict upper bound on the original
;; interval, under the stated region and C integer-range hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun subs0-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun subs0-address-base (address)
  (car address))

(defun subs0-address-offset (address)
  (cdr address))

(defun subs0-shift (address amount)
  (cons
   (subs0-address-base address)
   (+ (subs0-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; integer memory t and region function.

(defstub subs0-integer-memory (address) t)
(defstub subs0-region (base) t)

(defun-sk subs0-function-types-p ()
  (forall (address base)
    (and
     (implies
      (subs0-address-p address)
      (integerp (subs0-integer-memory address)))
     (implies
      (integerp base)
      (integerp (subs0-region base))))))

(defun subs0-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun subs0-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Exact unfolding of Axiomatic1.p_strictupperbound_1' over every
;; mathematical integer index.

(defun-sk subs0-strict-upper-bound-p (address lower upper value)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (<
      (subs0-integer-memory
       (subs0-shift address index))
      value))))

(defun-sk ntp4vc-strict-upper-bound-shift-post-goal0-statement ()
  (forall
   (i2 i1 address value)
   (implies
    (and
     (integerp i2)
     (integerp i1)
     (subs0-address-p address)
     (integerp value)
     (subs0-function-types-p))
    (implies
     (and
      (<= i2 i1)
      (<=
       (subs0-region (subs0-address-base address))
       0)
      (subs0-is-uint32-p i1)
      (subs0-is-uint32-p i2)
      (subs0-is-sint32-p value)
      (subs0-strict-upper-bound-p
       (subs0-shift address i2)
       0
       (- i1 i2)
       value))
     (subs0-strict-upper-bound-p
      address
      i2
      i1
      value)))))

(value-triple :itpeval-statement-checked)

:q
