;; Statement-only formalization of thousand-theorems corpus artifact
;; thousand-theorems__acl2__Q2226786, "Sperner's theorem": every finite
;; antichain of subsets of a finite set has cardinality at most the middle
;; binomial coefficient. This file contains no proof.

(in-package "ACL2")

;; Duplicate-free true lists enumerate finite types and their finite subsets.
;; Extensional equality below makes the representation independent of list
;; order. Thus the valid families represent exactly Finset (Finset alpha).

(defun q2226786-carrier-p (carrier)
  (and (true-listp carrier)
       (no-duplicatesp-equal carrier)))

(defun q2226786-subset-p (left right)
  (if (consp left)
      (and (member-equal (car left) right)
           (q2226786-subset-p (cdr left) right))
    t))

(defun q2226786-finite-subset-p (set carrier)
  (and (true-listp set)
       (no-duplicatesp-equal set)
       (q2226786-subset-p set carrier)))

(defun q2226786-set-equal-p (left right)
  (and (q2226786-subset-p left right)
       (q2226786-subset-p right left)))

(defun q2226786-set-distinct-from-family-p (set family)
  (if (consp family)
      (and (not (q2226786-set-equal-p set (car family)))
           (q2226786-set-distinct-from-family-p
            set (cdr family)))
    t))

(defun q2226786-family-p (family carrier)
  (if (consp family)
      (and (q2226786-finite-subset-p (car family) carrier)
           (q2226786-set-distinct-from-family-p
            (car family) (cdr family))
           (q2226786-family-p (cdr family) carrier))
    (equal family nil)))

(defun q2226786-incomparable-with-family-p (set family)
  (if (consp family)
      (and (not (q2226786-subset-p set (car family)))
           (not (q2226786-subset-p (car family) set))
           (q2226786-incomparable-with-family-p
            set (cdr family)))
    t))

(defun q2226786-antichain-p (family)
  (if (consp family)
      (and (q2226786-incomparable-with-family-p
            (car family) (cdr family))
           (q2226786-antichain-p (cdr family)))
    (equal family nil)))

(defun q2226786-binomial-coefficient (n k)
  (declare (xargs :measure (nfix n)))
  (if (or (zp k)
          (zp n))
      (if (zp k) 1 0)
    (+ (q2226786-binomial-coefficient (- n 1) k)
       (q2226786-binomial-coefficient (- n 1) (- k 1)))))

(defun thousand-theorems-q2226786-sperners-theorem-statement
    (carrier family)
  (implies
   (and (q2226786-carrier-p carrier)
        (q2226786-family-p family carrier)
        (q2226786-antichain-p family))
   (<=
    (len family)
    (q2226786-binomial-coefficient
     (len carrier)
     (floor (len carrier) 2)))))

(value-triple :itpeval-statement-checked)
:q
