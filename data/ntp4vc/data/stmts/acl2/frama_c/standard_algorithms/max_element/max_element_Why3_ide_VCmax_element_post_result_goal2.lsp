;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/standard_algorithms/max_element/max_element_Why3_ide_VCmax_element_post_result_goal2:
;; nonnegativity of the integer result bound under the stated nonpositive,
;; region, linked-allocation, unsigned-32, and valid-read hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun meg2-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun meg2-address-base (address)
  (car address))

(defun meg2-address-offset (address)
  (cdr address))

(defun meg2-shift (address amount)
  (cons
   (meg2-address-base address)
   (+ (meg2-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; allocation map t, region function, and linked predicate specialized to t.

(defstub meg2-allocation (index) t)
(defstub meg2-region (base) t)
(defstub meg2-linked-op () t)

(defun-sk meg2-function-types-p ()
  (forall (index base)
    (and
     (implies
      (integerp index)
      (integerp (meg2-allocation index)))
     (implies
      (integerp base)
      (integerp (meg2-region base))))))

(defun meg2-linked-p ()
  (if (meg2-linked-op) t nil))

(defun meg2-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

;; Exact unfolding of Memory.valid_rd for the arbitrary allocation map t.

(defun meg2-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (meg2-address-base address)))
    (<= 0 (meg2-address-offset address))
    (<=
     (+ (meg2-address-offset address) length)
     (meg2-allocation (meg2-address-base address))))))

(defun-sk ntp4vc-max-element-post-result-goal2-statement ()
  (forall
   (i a)
   (implies
    (and
     (integerp i)
     (meg2-address-p a)
     (meg2-function-types-p))
    (implies
     (and
      (<= i 0)
      (<= (meg2-region (meg2-address-base a)) 0)
      (meg2-linked-p)
      (meg2-is-uint32-p i)
      (meg2-valid-rd-p (meg2-shift a 0) i))
     (<= 0 i)))))

(value-triple :itpeval-statement-checked)

:q
