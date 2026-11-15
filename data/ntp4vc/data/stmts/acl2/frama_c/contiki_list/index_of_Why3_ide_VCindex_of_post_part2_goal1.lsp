;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/index_of_Why3_ide_VCindex_of_post_part2_goal1:
;; correctness of the returned pointer-array index when the selected item has
;; no earlier occurrence in the searched interval. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun iof1-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun iof1-address-base (address)
  (car address))

(defun iof1-address-offset (address)
  (cdr address))

(defun iof1-shift (address amount)
  (cons
   (iof1-address-base address)
   (+ (iof1-address-offset address) amount)))

;; These conservative symbols represent the universally arbitrary source
;; pointer function t_1, integer function t, region and linked operations, and
;; the imported l_index_of operation specialized to t_1.

(defstub iof1-t1 (address) t)
(defstub iof1-t (index) t)
(defstub iof1-region (base) t)
(defstub iof1-linked-op () t)
(defstub iof1-l-index-of (item array down up) t)

(defun-sk iof1-function-types-p ()
  (forall (address index base item array down up)
    (implies
     (and
      (iof1-address-p address)
      (integerp index)
      (integerp base)
      (iof1-address-p item)
      (iof1-address-p array)
      (integerp down)
      (integerp up))
     (and
      (iof1-address-p (iof1-t1 address))
      (integerp (iof1-t index))
      (integerp (iof1-region base))
      (integerp
       (iof1-l-index-of item array down up))))))

(defun iof1-linked-p ()
  (if (iof1-linked-op) t nil))

(defun iof1-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun iof1-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (iof1-address-base address))
    (<= 0 (iof1-address-offset address))
    (<=
     (+ (iof1-address-offset address) length)
     (iof1-t (iof1-address-base address))))))

(defun-sk iof1-framed-p ()
  (forall (address)
    (implies
     (iof1-address-p address)
     (<=
      (iof1-region
       (iof1-address-base (iof1-t1 address)))
      0))))

;; These are exactly the three source axioms characterizing l_index_of for the
;; arbitrary pointer function t_1: exhausted interval, found item, and the
;; recursive step past a nonmatching item.

(defun-sk iof1-l-index-of-laws-p ()
  (forall (item array down up)
    (implies
     (and
      (iof1-address-p item)
      (iof1-address-p array)
      (integerp down)
      (integerp up))
     (and
      (implies
       (and
        (<= up down)
        (<= 0 up))
       (equal
        (iof1-l-index-of item array down up)
        up))
      (implies
       (and
        (equal (iof1-t1 (iof1-shift array down)) item)
        (<= 0 down)
        (< down up))
       (equal
        (iof1-l-index-of item array down up)
        down))
      (implies
       (and
        (not
         (equal (iof1-t1 (iof1-shift array down)) item))
        (<= 0 down)
        (< down up))
       (equal
        (iof1-l-index-of item array (+ 1 down) up)
        (iof1-l-index-of item array down up)))))))

(defun-sk iof1-no-earlier-item-p (item array lower selected)
  (forall (index)
    (implies
     (and
      (integerp index)
      (< index selected)
      (<= lower index))
     (not
      (equal
       item
       (iof1-t1 (iof1-shift array index)))))))

(defun-sk
    ntp4vc-index-of-post-part2-goal1-statement ()
  (forall
   (a i1 i i2)
   (implies
    (and
     (iof1-function-types-p)
     (iof1-l-index-of-laws-p)
     (iof1-address-p a)
     (integerp i1)
     (integerp i)
     (integerp i2))
    (let ((a1 (iof1-t1 (iof1-shift a i1))))
      (implies
       (and
        (<= 0 i)
        (<= i1 i)
        (< i1 i)
        (<= i2 i1)
        (<= 0 i2)
        (< i2 i)
        (<= (iof1-region (iof1-address-base a)) 0)
        (<= (iof1-region (iof1-address-base a1)) 0)
        (iof1-framed-p)
        (iof1-linked-p)
        (iof1-is-sint32-p i)
        (iof1-is-sint32-p i1)
        (iof1-is-sint32-p i2)
        (implies
         (<= i2 i)
         (iof1-valid-rw-p
          (iof1-shift a i2)
          (- i i2)))
        (iof1-no-earlier-item-p a1 a i2 i1))
       (equal
        (iof1-l-index-of a1 a i2 i)
        i1))))))

(value-triple :itpeval-statement-checked)

:q
