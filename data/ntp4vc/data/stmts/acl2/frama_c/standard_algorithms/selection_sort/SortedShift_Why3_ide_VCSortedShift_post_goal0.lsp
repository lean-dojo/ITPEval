;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/selection_sort/SortedShift_Why3_ide_VCSortedShift_post_goal0:
;; shifting the base of a sorted integer-memory interval to its lower endpoint
;; preserves sortedness over the corresponding zero-based interval, under the
;; stated region and unsigned 32-bit hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun sss0-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun sss0-address-base (address)
  (car address))

(defun sss0-address-offset (address)
  (cdr address))

(defun sss0-shift (address amount)
  (cons
   (sss0-address-base address)
   (+ (sss0-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; integer memory t and region function.

(defstub sss0-integer-memory (address) t)
(defstub sss0-region (base) t)

(defun-sk sss0-function-types-p ()
  (forall (address base)
    (and
     (implies
      (sss0-address-p address)
      (integerp (sss0-integer-memory address)))
     (implies
      (integerp base)
      (integerp (sss0-region base))))))

(defun sss0-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

;; Exact unfolding of Axiomatic1.p_sorted_1' over every pair of mathematical
;; integer indices.

(defun-sk sss0-sorted-p (address lower upper)
  (forall (left right)
    (implies
     (and
      (integerp left)
      (integerp right)
      (< right upper)
      (<= lower left)
      (< left right))
     (<=
      (sss0-integer-memory
       (sss0-shift address left))
      (sss0-integer-memory
       (sss0-shift address right))))))

(defun-sk ntp4vc-sorted-shift-post-goal0-statement ()
  (forall
   (i1 i address)
   (implies
    (and
     (integerp i1)
     (integerp i)
     (sss0-address-p address)
     (sss0-function-types-p))
    (implies
     (and
      (<= i1 i)
      (<=
       (sss0-region (sss0-address-base address))
       0)
      (sss0-is-uint32-p i)
      (sss0-is-uint32-p i1)
      (sss0-sorted-p address i1 i))
     (sss0-sorted-p
      (sss0-shift address i1)
      0
      (- i i1))))))

(value-triple :itpeval-statement-checked)

:q
