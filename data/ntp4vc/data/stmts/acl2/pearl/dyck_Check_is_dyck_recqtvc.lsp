;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/dyck_Check_is_dyck_recqtvc: uniqueness and recursive propagation of
;; valid Dyck-word prefix decompositions. This file contains no proof.

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

(defun-sk ntp4vc-dyck-no-fall-splitsp (word)
  (forall (prefix suffix)
    (implies
     (and
      (ntp4vc-dyck-paren-listp prefix)
      (ntp4vc-dyck-paren-listp suffix)
      (equal word (append prefix suffix)))
     (not (ntp4vc-dyck-fallp prefix suffix)))))

(defun-sk ntp4vc-dyck-all-inner-suffixes-p
    (word inner-word outer-prefix inner-prefix)
  (forall (inner-suffix)
    (implies
     (and
      (ntp4vc-dyck-paren-listp inner-suffix)
      (equal inner-word (append inner-prefix inner-suffix))
      (ntp4vc-dyck-fallp inner-prefix inner-suffix)
      (ntp4vc-dyck-unique-fall-splitp
       inner-word inner-prefix inner-suffix))
     (let ((combined-prefix
            (cons 'L
                  (append outer-prefix
                          (cons 'R inner-prefix)))))
       (and
        (equal word (append combined-prefix inner-suffix))
        (ntp4vc-dyck-fallp combined-prefix inner-suffix)
        (ntp4vc-dyck-unique-fall-splitp
         word combined-prefix inner-suffix))))))

(defun-sk ntp4vc-dyck-all-inner-prefixes-p
    (word inner-word outer-prefix)
  (forall (inner-prefix)
    (implies
     (ntp4vc-dyck-paren-listp inner-prefix)
     (and
      (ntp4vc-dyck-all-inner-suffixes-p
       word inner-word outer-prefix inner-prefix)
      (implies
       (ntp4vc-dyck-no-fall-splitsp inner-word)
       (ntp4vc-dyck-no-fall-splitsp word))))))

(defun ntp4vc-dyck-outer-suffix-resultp
    (word outer-prefix outer-suffix)
  (if (consp outer-suffix)
      (let ((inner-word (cdr outer-suffix)))
        (and
         (<= 0 (len word))
         (< (len inner-word) (len word))
         (ntp4vc-dyck-all-inner-prefixes-p
          word inner-word outer-prefix)))
    (ntp4vc-dyck-no-fall-splitsp word)))

(defun-sk ntp4vc-dyck-all-outer-suffixes-p
    (word tail outer-prefix)
  (forall (outer-suffix)
    (implies
     (and
      (ntp4vc-dyck-paren-listp outer-suffix)
      (equal tail (append outer-prefix outer-suffix))
      (ntp4vc-dyck-fallp outer-prefix outer-suffix)
      (ntp4vc-dyck-unique-fall-splitp
       tail outer-prefix outer-suffix))
     (ntp4vc-dyck-outer-suffix-resultp
      word outer-prefix outer-suffix))))

(defun-sk ntp4vc-dyck-all-outer-prefixes-p (word tail)
  (forall (outer-prefix)
    (implies
     (ntp4vc-dyck-paren-listp outer-prefix)
     (and
      (ntp4vc-dyck-all-outer-suffixes-p
       word tail outer-prefix)
      (implies
       (ntp4vc-dyck-no-fall-splitsp tail)
       (ntp4vc-dyck-no-fall-splitsp word))))))

(defun ntp4vc-dyck-is-dyck-rec-bodyp (word)
  (if (and (consp word)
           (equal (car word) 'L))
      (let ((tail (cdr word)))
        (and
         (<= 0 (len word))
         (< (len tail) (len word))
         (ntp4vc-dyck-all-outer-prefixes-p word tail)))
    (and
     (equal word (append nil word))
     (ntp4vc-dyck-fallp nil word)
     (ntp4vc-dyck-unique-fall-splitp word nil word))))

(defun-sk ntp4vc-dyck-check-is-dyck-recqtvc-statement ()
  (forall (word)
    (implies
     (ntp4vc-dyck-paren-listp word)
     (ntp4vc-dyck-is-dyck-rec-bodyp word))))

(value-triple :itpeval-statement-checked)
:q
