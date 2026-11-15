;; Statement-only formalization of Logipedia corpus artifact bool.bool_discr,
;; catalog title "bool.bool_discr": for equal Boolean values x and y, the
;; nested Boolean eliminator selects (forall P, P -> P) rather than
;; (forall P, P). This file contains no proof.

(in-package "ACL2")

;; In a proposition-valued ACL2 body, the two closed source propositions
;; (forall P, P -> P) and (forall P, P) have truth values t and nil.

(defun logipedia-bool-discr-match-prop
    (case-true case-false boolean-value)
  (if (equal boolean-value t)
      case-true
    case-false))

(defun logipedia-bool-discr-statement (x y)
  (implies
   (and (booleanp x)
        (booleanp y))
   (implies
    (equal x y)
    (logipedia-bool-discr-match-prop
     (logipedia-bool-discr-match-prop t nil y)
     (logipedia-bool-discr-match-prop nil t y)
     x))))

(value-triple :itpeval-statement-checked)
:q
