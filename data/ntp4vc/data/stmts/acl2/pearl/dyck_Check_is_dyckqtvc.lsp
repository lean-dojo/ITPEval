;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/dyck_Check_is_dyckqtvc: correctness of a Dyck-word check from a
;; unique valid prefix split, and rejection when no such split exists.
;; This file contains no proof.

(in-package "ACL2")

;; L and R are the two constructors of the source paren type.

(defun ntp4vc-dyck-parenp (x)
  (or (equal x 'L)
      (equal x 'R)))

(defun ntp4vc-dyck-paren-listp (xs)
  (if (consp xs)
      (and (ntp4vc-dyck-parenp (car xs))
           (ntp4vc-dyck-paren-listp (cdr xs)))
    (equal xs nil)))

;; Scanning at depth zero recognizes exactly the inductively generated Dyck
;; language: nil, or L followed by a Dyck word, R, and another Dyck word.

(defun ntp4vc-dyck-scanp (xs depth)
  (if (consp xs)
      (if (equal (car xs) 'L)
          (ntp4vc-dyck-scanp (cdr xs) (+ depth 1))
        (and (equal (car xs) 'R)
             (< 0 depth)
             (ntp4vc-dyck-scanp (cdr xs) (- depth 1))))
    (and (equal xs nil)
         (equal depth 0))))

(defun ntp4vc-dyck-wordp (xs)
  (and (ntp4vc-dyck-paren-listp xs)
       (ntp4vc-dyck-scanp xs 0)))

(defun ntp4vc-dyck-fallp (prefix suffix)
  (and (ntp4vc-dyck-wordp prefix)
       (not (and (consp suffix)
                 (equal (car suffix) 'L)))))

;; This is the source statement's uniqueness condition for a fall split.

(defun-sk ntp4vc-dyck-unique-fall-splitp
    (word chosen-prefix chosen-suffix)
  (forall (prefix suffix)
    (implies
     (and
      (ntp4vc-dyck-paren-listp prefix)
      (ntp4vc-dyck-paren-listp suffix)
      (equal word (append prefix suffix))
      (ntp4vc-dyck-fallp prefix suffix))
     (and
      (equal prefix chosen-prefix)
      (equal suffix chosen-suffix)))))

;; The Boolean result is true exactly when the whole word is a Dyck word,
;; under the source match condition determined by the chosen suffix.

(defun-sk ntp4vc-dyck-result-characterizationp
    (word chosen-suffix)
  (forall (result)
    (implies
     (and
      (booleanp result)
      (if (equal chosen-suffix nil)
          (equal result t)
        (equal result nil)))
     (iff
      (equal result t)
      (ntp4vc-dyck-wordp word)))))

(defun-sk ntp4vc-dyck-all-chosen-suffixes-p
    (word chosen-prefix)
  (forall (chosen-suffix)
    (implies
     (and
      (ntp4vc-dyck-paren-listp chosen-suffix)
      (equal word (append chosen-prefix chosen-suffix))
      (ntp4vc-dyck-fallp chosen-prefix chosen-suffix)
      (ntp4vc-dyck-unique-fall-splitp
       word chosen-prefix chosen-suffix))
     (ntp4vc-dyck-result-characterizationp
      word chosen-suffix))))

(defun-sk ntp4vc-dyck-no-fall-splitsp (word)
  (forall (prefix suffix)
    (implies
     (and
      (ntp4vc-dyck-paren-listp prefix)
      (ntp4vc-dyck-paren-listp suffix)
      (equal word (append prefix suffix)))
     (not (ntp4vc-dyck-fallp prefix suffix)))))

(defun ntp4vc-pearl-dyck-check-is-dyckqtvc-statement
    (word chosen-prefix)
  (implies
   (and
    (ntp4vc-dyck-paren-listp word)
    (ntp4vc-dyck-paren-listp chosen-prefix))
   (and
    (ntp4vc-dyck-all-chosen-suffixes-p
     word chosen-prefix)
    (implies
     (ntp4vc-dyck-no-fall-splitsp word)
     (not (ntp4vc-dyck-wordp word))))))

(value-triple :itpeval-statement-checked)
:q
