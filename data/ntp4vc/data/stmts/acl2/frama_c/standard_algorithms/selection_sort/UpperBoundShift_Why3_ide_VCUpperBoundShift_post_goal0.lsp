;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/selection_sort/UpperBoundShift_Why3_ide_VCUpperBoundShift_post_goal0:
;; shifting an array base to the lower endpoint of an upper-bound interval
;; preserves the corresponding upper bound on the original interval, under
;; the stated region and C integer-range hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun ubs0-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun ubs0-address-base (address)
  (car address))

(defun ubs0-address-offset (address)
  (cdr address))

(defun ubs0-shift (address amount)
  (cons
   (ubs0-address-base address)
   (+ (ubs0-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; integer memory t and region function.

(defstub ubs0-integer-memory (address) t)
(defstub ubs0-region (base) t)

(defun-sk ubs0-function-types-p ()
  (forall (address base)
    (and
     (implies
      (ubs0-address-p address)
      (integerp (ubs0-integer-memory address)))
     (implies
      (integerp base)
      (integerp (ubs0-region base))))))

(defun ubs0-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun ubs0-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Exact unfolding of Axiomatic1.p_upperbound_1' over every mathematical
;; integer index.

(defun-sk ubs0-upper-bound-p (address lower upper value)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (<=
      (ubs0-integer-memory
       (ubs0-shift address index))
      value))))

(defun-sk ntp4vc-upper-bound-shift-post-goal0-statement ()
  (forall
   (i2 i1 address value)
   (implies
    (and
     (integerp i2)
     (integerp i1)
     (ubs0-address-p address)
     (integerp value)
     (ubs0-function-types-p))
    (implies
     (and
      (<= i2 i1)
      (<=
       (ubs0-region (ubs0-address-base address))
       0)
      (ubs0-is-uint32-p i1)
      (ubs0-is-uint32-p i2)
      (ubs0-is-sint32-p value)
      (ubs0-upper-bound-p
       (ubs0-shift address i2)
       0
       (- i1 i2)
       value))
     (ubs0-upper-bound-p
      address
      i2
      i1
      value)))))

(value-triple :itpeval-statement-checked)

:q
