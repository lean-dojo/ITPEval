;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/__tolower_Why3_ide_VC__tolower_post_goal0:
;; correctness of the ASCII lowercase result selected from an unsigned byte,
;; according to whether its signed-byte interpretation is uppercase.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

(defun tl0-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun tl0-to-uint8 (value)
  (mod (ifix value) 256))

(defun tl0-to-sint8 (value)
  (let ((unsigned-value (tl0-to-uint8 value)))
    (if (< unsigned-value 128)
        unsigned-value
      (- unsigned-value 256))))

(defun tl0-p-isupper (value)
  (and
   (integerp value)
   (<= 65 value)
   (<= value 90)))

;; The source axioms for l_tolower are equivalent over the integers to this
;; piecewise ASCII definition: uppercase codes are shifted by 32 and every
;; other integer is unchanged.

(defun tl0-l-tolower (value)
  (if (tl0-p-isupper value)
      (+ value 32)
    value))

(defun-sk ntp4vc-tolower-post-goal0-statement ()
  (forall
   (i-1 i i-2)
   (implies
    (and
     (integerp i-1)
     (integerp i)
     (integerp i-2)
     (iff
      (tl0-p-isupper (tl0-to-sint8 i-1))
      (not (equal i 0)))
     (tl0-is-uint8-p i)
     (tl0-is-uint8-p i-1)
     (tl0-is-uint8-p i-2)
     (if (equal i 0)
         (equal i-2 i-1)
       (equal (tl0-to-uint8 (+ 32 i-1)) i-2)))
    (equal (tl0-l-tolower i-1) i-2))))

(value-triple :itpeval-statement-checked)

:q
