;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/mergesort_list_OCamlMergesort_chopqtvc: the list-chop verification
;; condition for a bounded prefix length and reconstruction from the tail.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These conservative interfaces represent the arbitrary inhabited source
;; element type and its polymorphic prefix operation.

(defstub msc-element-p (x) t)
(defstub msc-default-element () t)
(defstub msc-prefix1 (n xs) t)

(defun msc-list-p (xs)
  (if (consp xs)
      (and
       (msc-element-p (car xs))
       (msc-list-p (cdr xs)))
    (equal xs nil)))

(defun-sk msc-prefix-typed-p ()
  (forall (n xs)
    (implies
     (and
      (integerp n)
      (msc-list-p xs))
     (msc-list-p (msc-prefix1 n xs)))))

(defun-sk msc-prefix-zero-law-p ()
  (forall (xs)
    (implies
     (msc-list-p xs)
     (equal (msc-prefix1 0 xs) nil))))

(defun-sk msc-prefix-cons-law-p ()
  (forall (n x xs)
    (implies
     (and
      (integerp n)
      (< 0 n)
      (msc-element-p x)
      (msc-list-p xs))
     (equal
      (msc-prefix1 n (cons x xs))
      (cons x (msc-prefix1 (- n 1) xs))))))

(defun msc-interface-p ()
  (and
   (msc-element-p (msc-default-element))
   (msc-prefix-typed-p)
   (msc-prefix-zero-law-p)
   (msc-prefix-cons-law-p)))

;; This is the source recursive-call side condition when n is nonzero.

(defun msc-tail-call-bounds-p (n l)
  (implies
   (not (equal n 0))
   (if (consp l)
       (let ((o1 (- n 1)))
         (and
          (and
           (<= 0 n)
           (< o1 n))
          (<= 0 o1)
          (<= o1 (len (cdr l)))))
     nil)))

;; The result list remains universally quantified inside the conclusion.

(defun-sk msc-all-results-reconstruct-p (n l)
  (forall (result)
    (implies
     (msc-list-p result)
     (implies
      (if (equal n 0)
          (equal result l)
        (if (consp l)
            (equal
             (cdr l)
             (append
              (msc-prefix1 (- n 1) (cdr l))
              result))
          nil))
      (equal
       l
       (append (msc-prefix1 n l) result))))))

(defun
  ntp4vc-pearl-mergesort-list-ocamlmergesort-chopqtvc-statement
  (n l)
  (implies
   (and
    (msc-interface-p)
    (integerp n)
    (msc-list-p l)
    (<= 0 n)
    (<= n (len l)))
   (and
    (msc-tail-call-bounds-p n l)
    (msc-all-results-reconstruct-p n l))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
