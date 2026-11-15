;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/__toupper_Why3_ide_VC__toupper_post_goal0:
;; correctness of ASCII uppercasing with the source's abstract signed- and
;; unsigned-byte conversions constrained by their explicit Cint laws.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

(defun tu0-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun tu0-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

;; Conservative interfaces preserve the source's abstract Cint operations.

(defstub tu0-to-uint8 (value) t)

(defstub tu0-to-sint8 (value) t)

;; These are the source's explicit Cint range, identity, and projection laws
;; for to_uint8 and to_sint8, universally closed over their integer domain.

(defun-sk tu0-cint-laws-p ()
  (forall
   (value)
   (implies
    (integerp value)
    (and
     (tu0-is-uint8-p (tu0-to-uint8 value))
     (tu0-is-sint8-p (tu0-to-sint8 value))
     (implies
      (tu0-is-uint8-p value)
      (equal (tu0-to-uint8 value) value))
     (implies
      (tu0-is-sint8-p value)
      (equal (tu0-to-sint8 value) value))
     (equal
      (tu0-to-uint8 (tu0-to-uint8 value))
      (tu0-to-uint8 value))
     (equal
      (tu0-to-sint8 (tu0-to-sint8 value))
      (tu0-to-sint8 value))
     (equal
      (tu0-to-sint8 (tu0-to-uint8 value))
      (tu0-to-sint8 value))))))

(defun tu0-p-islower (value)
  (and
   (integerp value)
   (<= 97 value)
   (<= value 122)))

;; The source axioms for l_toupper are equivalent over the integers to this
;; piecewise ASCII definition: lowercase codes are shifted by -32 and every
;; other integer is unchanged.

(defun tu0-l-toupper (value)
  (if (tu0-p-islower value)
      (- value 32)
    value))

(defun-sk ntp4vc-toupper-post-goal0-statement ()
  (forall
   (i-1 i i-2)
   (implies
    (and
     (tu0-cint-laws-p)
     (integerp i-1)
     (integerp i)
     (integerp i-2)
     (iff
      (tu0-p-islower (tu0-to-sint8 i-1))
      (not (equal i 0)))
     (tu0-is-uint8-p i)
     (tu0-is-uint8-p i-1)
     (tu0-is-uint8-p i-2)
     (if (equal i 0)
         (equal i-2 i-1)
       (equal (tu0-to-uint8 (- i-1 32)) i-2)))
    (equal (tu0-l-toupper i-1) i-2))))

(value-triple :itpeval-statement-checked)

:q
