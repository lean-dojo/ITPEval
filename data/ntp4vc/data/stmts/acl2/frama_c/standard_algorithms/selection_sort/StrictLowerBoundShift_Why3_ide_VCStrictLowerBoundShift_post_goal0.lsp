;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/selection_sort/StrictLowerBoundShift_Why3_ide_VCStrictLowerBoundShift_post_goal0:
;; shifting an array base and its strict-lower-bound interval by the same
;; integer amount preserves the strict-lower-bound property, under the stated
;; region and C integer-range hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun slbs0-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun slbs0-address-base (address)
  (car address))

(defun slbs0-address-offset (address)
  (cdr address))

(defun slbs0-shift (address amount)
  (cons
   (slbs0-address-base address)
   (+ (slbs0-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; integer memory t and region function.

(defstub slbs0-integer-memory (address) t)
(defstub slbs0-region (base) t)

(defun-sk slbs0-function-types-p ()
  (forall (address base)
    (and
     (implies
      (slbs0-address-p address)
      (integerp (slbs0-integer-memory address)))
     (implies
      (integerp base)
      (integerp (slbs0-region base))))))

(defun slbs0-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun slbs0-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Exact unfolding of Axiomatic1.p_strictlowerbound_1' over every
;; mathematical integer index.

(defun-sk slbs0-strict-lower-bound-p (address lower upper value)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (<
      value
      (slbs0-integer-memory
       (slbs0-shift address index))))))

(defun-sk ntp4vc-strict-lower-bound-shift-post-goal0-statement ()
  (forall
   (i1 i3 address i2 value)
   (implies
    (and
     (integerp i1)
     (integerp i3)
     (slbs0-address-p address)
     (integerp i2)
     (integerp value)
     (slbs0-function-types-p))
    (let ((x (+ i1 i3)))
      (implies
       (and
        (<=
         (slbs0-region (slbs0-address-base address))
         0)
        (<= x 4294967295)
        (slbs0-is-uint32-p i1)
        (slbs0-is-uint32-p i2)
        (slbs0-is-uint32-p i3)
        (slbs0-is-sint32-p value)
        (slbs0-strict-lower-bound-p
         (slbs0-shift address i3)
         i2 i1 value))
       (slbs0-strict-lower-bound-p
        address
        (+ i2 i3)
        x
        value))))))

(value-triple :itpeval-statement-checked)

:q
