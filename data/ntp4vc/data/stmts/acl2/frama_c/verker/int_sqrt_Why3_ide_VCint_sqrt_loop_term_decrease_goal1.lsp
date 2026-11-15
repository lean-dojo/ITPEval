;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/int_sqrt_Why3_ide_VCint_sqrt_loop_term_decrease_goal1:
;; a two-bit logical right shift strictly decreases a nonzero unsigned 64-bit
;; loop value under the verification condition's range hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(defun int-sqrt-goal1-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; On the source's nonnegative integer domain, logical right shift by two bits
;; is exactly floor division by 4.

(defun int-sqrt-goal1-lsr-two (value)
  (floor (ifix value) 4))

(defun-sk ntp4vc-int-sqrt-loop-term-decrease-goal1-statement ()
  (forall
   (i-1 i)
   (let ((x (int-sqrt-goal1-lsr-two i-1)))
     (implies
      (and
       (not (equal i-1 0))
       (<= 2 i)
       (int-sqrt-goal1-is-uint64-p i)
       (int-sqrt-goal1-is-uint64-p i-1)
       (int-sqrt-goal1-is-uint64-p x))
      (< x i-1)))))

(value-triple :itpeval-statement-checked)

:q
