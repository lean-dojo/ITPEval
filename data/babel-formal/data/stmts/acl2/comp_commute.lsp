;; Statement-only formalization of Babel-formal artifact comp_commute:
;; composition and identity laws for arbitrary functions between arbitrary
;; carriers, together with basic properties of commuting endofunctions. This
;; file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; ACL2 is first order, so each source-level function and carrier variable is
;; represented by a theorem-specific conservative DEFSTUB.  The predicates
;; below state all typing, equality, and commutation conditions explicitly.

(defun comp-commute-id (x)
  x)

;; comp_assoc

(defstub comp-commute-assoc-alpha-p (x) t)
(defstub comp-commute-assoc-beta-p (x) t)
(defstub comp-commute-assoc-gamma-p (x) t)
(defstub comp-commute-assoc-delta-p (x) t)
(defstub comp-commute-assoc-f (x) t)
(defstub comp-commute-assoc-g (x) t)
(defstub comp-commute-assoc-h (x) t)

(defun-sk comp-commute-assoc-typed-p ()
  (forall (x)
    (and
     (implies
      (comp-commute-assoc-alpha-p x)
      (comp-commute-assoc-beta-p
       (comp-commute-assoc-f x)))
     (implies
      (comp-commute-assoc-beta-p x)
      (comp-commute-assoc-gamma-p
       (comp-commute-assoc-g x)))
     (implies
      (comp-commute-assoc-gamma-p x)
      (comp-commute-assoc-delta-p
       (comp-commute-assoc-h x))))))

(defun-sk comp-commute-assoc-equality-p ()
  (forall (x)
    (implies
     (comp-commute-assoc-alpha-p x)
     (equal
      (comp-commute-assoc-h
       (comp-commute-assoc-g
        (comp-commute-assoc-f x)))
      (comp-commute-assoc-h
       (comp-commute-assoc-g
        (comp-commute-assoc-f x)))))))

(defun comp-commute-comp-assoc-statement ()
  (implies
   (comp-commute-assoc-typed-p)
   (comp-commute-assoc-equality-p)))

;; comp_id_l

(defstub comp-commute-id-l-alpha-p (x) t)
(defstub comp-commute-id-l-beta-p (x) t)
(defstub comp-commute-id-l-f (x) t)

(defun-sk comp-commute-id-l-typed-p ()
  (forall (x)
    (implies
     (comp-commute-id-l-alpha-p x)
     (comp-commute-id-l-beta-p
      (comp-commute-id-l-f x)))))

(defun-sk comp-commute-id-l-equality-p ()
  (forall (x)
    (implies
     (comp-commute-id-l-alpha-p x)
     (equal
      (comp-commute-id
       (comp-commute-id-l-f x))
      (comp-commute-id-l-f x)))))

(defun comp-commute-comp-id-l-statement ()
  (implies
   (comp-commute-id-l-typed-p)
   (comp-commute-id-l-equality-p)))

;; comp_id_r

(defstub comp-commute-id-r-alpha-p (x) t)
(defstub comp-commute-id-r-beta-p (x) t)
(defstub comp-commute-id-r-f (x) t)

(defun-sk comp-commute-id-r-typed-p ()
  (forall (x)
    (implies
     (comp-commute-id-r-alpha-p x)
     (comp-commute-id-r-beta-p
      (comp-commute-id-r-f x)))))

(defun-sk comp-commute-id-r-equality-p ()
  (forall (x)
    (implies
     (comp-commute-id-r-alpha-p x)
     (equal
      (comp-commute-id-r-f
       (comp-commute-id x))
      (comp-commute-id-r-f x)))))

(defun comp-commute-comp-id-r-statement ()
  (implies
   (comp-commute-id-r-typed-p)
   (comp-commute-id-r-equality-p)))

;; commute_symm

(defstub comp-commute-symm-alpha-p (x) t)
(defstub comp-commute-symm-f (x) t)
(defstub comp-commute-symm-g (x) t)

(defun-sk comp-commute-symm-hypotheses-p ()
  (forall (x)
    (implies
     (comp-commute-symm-alpha-p x)
     (and
      (comp-commute-symm-alpha-p
       (comp-commute-symm-f x))
      (comp-commute-symm-alpha-p
       (comp-commute-symm-g x))
      (equal
       (comp-commute-symm-f
        (comp-commute-symm-g x))
       (comp-commute-symm-g
        (comp-commute-symm-f x)))))))

(defun-sk comp-commute-symm-conclusion-p ()
  (forall (x)
    (implies
     (comp-commute-symm-alpha-p x)
     (equal
      (comp-commute-symm-g
       (comp-commute-symm-f x))
      (comp-commute-symm-f
       (comp-commute-symm-g x))))))

(defun comp-commute-symm-statement ()
  (implies
   (comp-commute-symm-hypotheses-p)
   (comp-commute-symm-conclusion-p)))

;; commute_with_id_l

(defstub comp-commute-with-id-l-alpha-p (x) t)
(defstub comp-commute-with-id-l-f (x) t)

(defun-sk comp-commute-with-id-l-typed-p ()
  (forall (x)
    (implies
     (comp-commute-with-id-l-alpha-p x)
     (comp-commute-with-id-l-alpha-p
      (comp-commute-with-id-l-f x)))))

(defun-sk comp-commute-with-id-l-conclusion-p ()
  (forall (x)
    (implies
     (comp-commute-with-id-l-alpha-p x)
     (equal
      (comp-commute-with-id-l-f
       (comp-commute-id x))
      (comp-commute-id
       (comp-commute-with-id-l-f x))))))

(defun comp-commute-with-id-l-statement ()
  (implies
   (comp-commute-with-id-l-typed-p)
   (comp-commute-with-id-l-conclusion-p)))

;; commute_with_id_r

(defstub comp-commute-with-id-r-alpha-p (x) t)
(defstub comp-commute-with-id-r-f (x) t)

(defun-sk comp-commute-with-id-r-typed-p ()
  (forall (x)
    (implies
     (comp-commute-with-id-r-alpha-p x)
     (comp-commute-with-id-r-alpha-p
      (comp-commute-with-id-r-f x)))))

(defun-sk comp-commute-with-id-r-conclusion-p ()
  (forall (x)
    (implies
     (comp-commute-with-id-r-alpha-p x)
     (equal
      (comp-commute-id
       (comp-commute-with-id-r-f x))
      (comp-commute-with-id-r-f
       (comp-commute-id x))))))

(defun comp-commute-with-id-r-statement ()
  (implies
   (comp-commute-with-id-r-typed-p)
   (comp-commute-with-id-r-conclusion-p)))

;; commute_refl

(defstub comp-commute-refl-alpha-p (x) t)
(defstub comp-commute-refl-f (x) t)

(defun-sk comp-commute-refl-typed-p ()
  (forall (x)
    (implies
     (comp-commute-refl-alpha-p x)
     (comp-commute-refl-alpha-p
      (comp-commute-refl-f x)))))

(defun-sk comp-commute-refl-conclusion-p ()
  (forall (x)
    (implies
     (comp-commute-refl-alpha-p x)
     (equal
      (comp-commute-refl-f
       (comp-commute-refl-f x))
      (comp-commute-refl-f
       (comp-commute-refl-f x))))))

(defun comp-commute-refl-statement ()
  (implies
   (comp-commute-refl-typed-p)
   (comp-commute-refl-conclusion-p)))

;; commute_congr

(defstub comp-commute-congr-alpha-p (x) t)
(defstub comp-commute-congr-f1 (x) t)
(defstub comp-commute-congr-f2 (x) t)
(defstub comp-commute-congr-g1 (x) t)
(defstub comp-commute-congr-g2 (x) t)

(defun-sk comp-commute-congr-hypotheses-p ()
  (forall (x)
    (implies
     (comp-commute-congr-alpha-p x)
     (and
      (comp-commute-congr-alpha-p
       (comp-commute-congr-f1 x))
      (comp-commute-congr-alpha-p
       (comp-commute-congr-f2 x))
      (comp-commute-congr-alpha-p
       (comp-commute-congr-g1 x))
      (comp-commute-congr-alpha-p
       (comp-commute-congr-g2 x))
      (equal
       (comp-commute-congr-f1 x)
       (comp-commute-congr-f2 x))
      (equal
       (comp-commute-congr-g1 x)
       (comp-commute-congr-g2 x))
      (equal
       (comp-commute-congr-f1
        (comp-commute-congr-g1 x))
       (comp-commute-congr-g1
        (comp-commute-congr-f1 x)))))))

(defun-sk comp-commute-congr-conclusion-p ()
  (forall (x)
    (implies
     (comp-commute-congr-alpha-p x)
     (equal
      (comp-commute-congr-f2
       (comp-commute-congr-g2 x))
      (comp-commute-congr-g2
       (comp-commute-congr-f2 x))))))

(defun comp-commute-congr-statement ()
  (implies
   (comp-commute-congr-hypotheses-p)
   (comp-commute-congr-conclusion-p)))

;; commute_transport_left_id

(defstub comp-commute-transport-left-alpha-p (x) t)
(defstub comp-commute-transport-left-f (x) t)
(defstub comp-commute-transport-left-g (x) t)

(defun-sk comp-commute-transport-left-hypotheses-p ()
  (forall (x)
    (implies
     (comp-commute-transport-left-alpha-p x)
     (and
      (comp-commute-transport-left-alpha-p
       (comp-commute-transport-left-f x))
      (comp-commute-transport-left-alpha-p
       (comp-commute-transport-left-g x))
      (equal
       (comp-commute-transport-left-f
        (comp-commute-transport-left-g x))
       (comp-commute-transport-left-g
        (comp-commute-transport-left-f x)))))))

(defun-sk comp-commute-transport-left-conclusion-p ()
  (forall (x)
    (implies
     (comp-commute-transport-left-alpha-p x)
     (equal
      (comp-commute-id
       (comp-commute-transport-left-f
        (comp-commute-transport-left-g x)))
      (comp-commute-transport-left-g
       (comp-commute-id
        (comp-commute-transport-left-f x)))))))

(defun comp-commute-transport-left-id-statement ()
  (implies
   (comp-commute-transport-left-hypotheses-p)
   (comp-commute-transport-left-conclusion-p)))

;; commute_transport_right_id

(defstub comp-commute-transport-right-alpha-p (x) t)
(defstub comp-commute-transport-right-f (x) t)
(defstub comp-commute-transport-right-g (x) t)

(defun-sk comp-commute-transport-right-hypotheses-p ()
  (forall (x)
    (implies
     (comp-commute-transport-right-alpha-p x)
     (and
      (comp-commute-transport-right-alpha-p
       (comp-commute-transport-right-f x))
      (comp-commute-transport-right-alpha-p
       (comp-commute-transport-right-g x))
      (equal
       (comp-commute-transport-right-f
        (comp-commute-transport-right-g x))
       (comp-commute-transport-right-g
        (comp-commute-transport-right-f x)))))))

(defun-sk comp-commute-transport-right-conclusion-p ()
  (forall (x)
    (implies
     (comp-commute-transport-right-alpha-p x)
     (equal
      (comp-commute-transport-right-f
       (comp-commute-id
        (comp-commute-transport-right-g x)))
      (comp-commute-id
       (comp-commute-transport-right-g
        (comp-commute-transport-right-f x)))))))

(defun comp-commute-transport-right-id-statement ()
  (implies
   (comp-commute-transport-right-hypotheses-p)
   (comp-commute-transport-right-conclusion-p)))

(value-triple :itpeval-statement-checked)
:q
