;; Statement-only formalization of Logipedia corpus artifact logic.not_to_not,
;; catalog title "logic.not_to_not": contraposition for arbitrary propositions,
;; stating under the imported False/Not introduction and elimination laws that
;; A implies B and Not B together imply Not A. This file contains no proof.

(in-package "ACL2")

;; ACL2 objects form the carrier of source propositions. These conservative
;; interfaces expose proposition truth and the imported module's abstract
;; False and Not constants. Their source laws are explicit predicates below.
(defstub logipedia-logic-not-to-not-holds-p
  (proposition)
  t)

(defstub logipedia-logic-not-to-not-false-proposition
  ()
  t)

(defstub logipedia-logic-not-to-not-not-proposition
  (proposition)
  t)

(defun-sk logipedia-logic-not-to-not-false-elimination-law-p ()
  (forall (q)
    (implies
     (logipedia-logic-not-to-not-holds-p
      (logipedia-logic-not-to-not-false-proposition))
     (logipedia-logic-not-to-not-holds-p q))))

(defun-sk logipedia-logic-not-to-not-introduction-law-p ()
  (forall (a)
    (implies
     (implies
      (logipedia-logic-not-to-not-holds-p a)
      (logipedia-logic-not-to-not-holds-p
       (logipedia-logic-not-to-not-false-proposition)))
     (logipedia-logic-not-to-not-holds-p
      (logipedia-logic-not-to-not-not-proposition a)))))

(defun-sk logipedia-logic-not-to-not-elimination-law-p ()
  (forall (a q)
    (implies
     (implies
      (implies
       (logipedia-logic-not-to-not-holds-p a)
       (logipedia-logic-not-to-not-holds-p
        (logipedia-logic-not-to-not-false-proposition)))
      (logipedia-logic-not-to-not-holds-p q))
     (implies
      (logipedia-logic-not-to-not-holds-p
       (logipedia-logic-not-to-not-not-proposition a))
      (logipedia-logic-not-to-not-holds-p q)))))

(defun-sk logipedia-logic-not-to-not-conclusion-p ()
  (forall (a b)
    (implies
     (implies
      (logipedia-logic-not-to-not-holds-p a)
      (logipedia-logic-not-to-not-holds-p b))
     (implies
      (logipedia-logic-not-to-not-holds-p
       (logipedia-logic-not-to-not-not-proposition b))
      (logipedia-logic-not-to-not-holds-p
       (logipedia-logic-not-to-not-not-proposition a))))))

(defun logipedia-logic-not-to-not-statement ()
  (implies
   (and
    (logipedia-logic-not-to-not-false-elimination-law-p)
    (logipedia-logic-not-to-not-introduction-law-p)
    (logipedia-logic-not-to-not-elimination-law-p))
   (logipedia-logic-not-to-not-conclusion-p)))

(value-triple :itpeval-statement-checked)
:q
