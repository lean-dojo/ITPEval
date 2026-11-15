;; Statement-only formalization of thousand-theorems corpus artifact Q4950096,
;; "Bourbaki–Witt theorem": every inflationary self-map of a nonempty
;; chain-complete partial order has a fixed point. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2 function objects give an extensional, potentially infinite
;; representation of the source carrier, order, self-map, and chain subsets.
;; In particular, a chain is a unary characteristic predicate, not a finite
;; list or table. All structure laws and all witnesses remain explicit below.

(defun q4950096-member-p (carrier x)
  (if (apply$ carrier (list x))
      t
    nil))

(defun q4950096-le-p (carrier order x y)
  (and
   (q4950096-member-p carrier x)
   (q4950096-member-p carrier y)
   (if (apply$ order (list x y))
       t
     nil)))

(defun q4950096-map-value (map x)
  (apply$ map (list x)))

(defun-sk q4950096-carrier-nonempty-p (carrier)
  (exists (x)
    (q4950096-member-p carrier x)))

(defun-sk q4950096-partial-order-p (carrier order)
  (forall (x y z)
    (and
     (implies
      (q4950096-member-p carrier x)
      (q4950096-le-p carrier order x x))
     (implies
      (and
       (q4950096-le-p carrier order x y)
       (q4950096-le-p carrier order y x))
      (equal x y))
     (implies
      (and
       (q4950096-le-p carrier order x y)
       (q4950096-le-p carrier order y z))
      (q4950096-le-p carrier order x z)))))

(defun-sk q4950096-map-typed-p (carrier map)
  (forall (x)
    (implies
     (q4950096-member-p carrier x)
     (q4950096-member-p
      carrier
      (q4950096-map-value map x)))))

(defun q4950096-chain-member-p (carrier chain x)
  (and
   (q4950096-member-p carrier x)
   (if (apply$ chain (list x))
       t
     nil)))

(defun-sk q4950096-chain-nonempty-p (carrier chain)
  (exists (x)
    (q4950096-chain-member-p carrier chain x)))

(defun-sk q4950096-chain-comparable-p
    (carrier order chain)
  (forall (x y)
    (implies
     (and
      (q4950096-chain-member-p carrier chain x)
      (q4950096-chain-member-p carrier chain y))
     (or
      (q4950096-le-p carrier order x y)
      (q4950096-le-p carrier order y x)))))

(defun q4950096-nonempty-chain-p
    (carrier order chain)
  (and
   (tamep-functionp chain)
   (q4950096-chain-nonempty-p carrier chain)
   (q4950096-chain-comparable-p
    carrier order chain)))

(defun-sk q4950096-below-bound-p
    (carrier order chain bound)
  (forall (x)
    (implies
     (q4950096-chain-member-p carrier chain x)
     (q4950096-le-p carrier order x bound))))

(defun q4950096-upper-bound-p
    (carrier order chain bound)
  (and
   (q4950096-member-p carrier bound)
   (q4950096-below-bound-p
    carrier order chain bound)))

(defun-sk q4950096-below-every-upper-bound-p
    (carrier order chain supremum)
  (forall (bound)
    (implies
     (q4950096-upper-bound-p
      carrier order chain bound)
     (q4950096-le-p
      carrier order supremum bound))))

(defun q4950096-least-upper-bound-p
    (carrier order chain supremum)
  (and
   (q4950096-upper-bound-p
    carrier order chain supremum)
   (q4950096-below-every-upper-bound-p
    carrier order chain supremum)))

(defun-sk q4950096-chain-supremum-exists-p
    (carrier order chain)
  (exists (supremum)
    (q4950096-least-upper-bound-p
     carrier order chain supremum)))

(defun-sk q4950096-chain-complete-p
    (carrier order)
  (forall (chain)
    (implies
     (q4950096-nonempty-chain-p
      carrier order chain)
     (q4950096-chain-supremum-exists-p
      carrier order chain))))

(defun-sk q4950096-inflationary-p
    (carrier order map)
  (forall (x)
    (implies
     (q4950096-member-p carrier x)
     (q4950096-le-p
      carrier order x
      (q4950096-map-value map x)))))

(defun-sk q4950096-fixed-point-exists-p
    (carrier map)
  (exists (x)
    (and
     (q4950096-member-p carrier x)
     (equal
      (q4950096-map-value map x)
      x))))

(defun thousand-theorems-q4950096-bourbaki-witt-theorem-statement
    (carrier order map)
  (implies
   (and
    (tamep-functionp carrier)
    (tamep-functionp order)
    (tamep-functionp map)
    (q4950096-carrier-nonempty-p carrier)
    (q4950096-partial-order-p carrier order)
    (q4950096-chain-complete-p carrier order)
    (q4950096-map-typed-p carrier map)
    (q4950096-inflationary-p
     carrier order map))
   (q4950096-fixed-point-exists-p
    carrier map)))

(value-triple :itpeval-statement-checked)
:q
