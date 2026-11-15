;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/selection_sort/LowerBoundShift_Why3_ide_VCLowerBoundShift_post_goal0:
;; shifting an array base and its lower-bound interval by the same integer
;; amount preserves the lower-bound property, under the stated region and
;; C integer-range hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lbs0-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lbs0-address-base (address)
  (car address))

(defun lbs0-address-offset (address)
  (cdr address))

(defun lbs0-shift (address amount)
  (cons
   (lbs0-address-base address)
   (+ (lbs0-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; integer memory t and region function.

(defstub lbs0-integer-memory (address) t)
(defstub lbs0-region (base) t)

(defun-sk lbs0-function-types-p ()
  (forall (address base)
    (and
     (implies
      (lbs0-address-p address)
      (integerp (lbs0-integer-memory address)))
     (implies
      (integerp base)
      (integerp (lbs0-region base))))))

(defun lbs0-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun lbs0-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Exact unfolding of Axiomatic1.p_lowerbound_1' over every mathematical
;; integer index.

(defun-sk lbs0-lower-bound-p (address lower upper value)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (<=
      value
      (lbs0-integer-memory
       (lbs0-shift address index))))))

(defun-sk ntp4vc-lower-bound-shift-post-goal0-statement ()
  (forall
   (i1 i3 address i2 value)
   (implies
    (and
     (integerp i1)
     (integerp i3)
     (lbs0-address-p address)
     (integerp i2)
     (integerp value)
     (lbs0-function-types-p))
    (let ((x (+ i1 i3)))
      (implies
       (and
        (<=
         (lbs0-region (lbs0-address-base address))
         0)
        (<= x 4294967295)
        (lbs0-is-uint32-p i1)
        (lbs0-is-uint32-p i2)
        (lbs0-is-uint32-p i3)
        (lbs0-is-sint32-p value)
        (lbs0-lower-bound-p
         (lbs0-shift address i3)
         i2 i1 value))
       (lbs0-lower-bound-p
        address
        (+ i2 i3)
        x
        value))))))

(value-triple :itpeval-statement-checked)

:q
