;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/word_common_factor_Top_powerqtvc: the recursive-power descent
;; verification condition stating that a nonzero nonnegative integer has a
;; nonnegative predecessor strictly smaller than itself. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

(defun
  ntp4vc-pearl-word-common-factor-top-powerqtvc-statement
  (n)
  (implies
   (and
    (integerp n)
    (<= 0 n)
    (not (equal n 0)))
   (let ((o1 (- n 1)))
     (and
      (and
       (<= 0 n)
       (< o1 n))
      (<= 0 o1)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
