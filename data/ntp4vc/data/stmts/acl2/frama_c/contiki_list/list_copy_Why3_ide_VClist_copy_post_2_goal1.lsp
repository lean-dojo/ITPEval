;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/list_copy_Why3_ide_VClist_copy_post_2_goal1:
;; preservation of an inductively defined linked-list segment after updating
;; one pointer cell under the stated memory and separation conditions.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lcp1-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lcp1-address-base (address)
  (car address))

(defun lcp1-address-offset (address)
  (cdr address))

(defun lcp1-shift (address amount)
  (cons
   (lcp1-address-base address)
   (+ (lcp1-address-offset address) amount)))

;; These conservative symbols represent the universally arbitrary source
;; pointer function t_1, integer function t, region operation, and linked
;; proposition specialized to t.

(defstub lcp1-t1 (address) t)
(defstub lcp1-t (index) t)
(defstub lcp1-region (base) t)
(defstub lcp1-linked-op () t)

(defun-sk lcp1-function-types-p ()
  (forall (address index base)
    (implies
     (and
      (lcp1-address-p address)
      (integerp index)
      (integerp base))
     (and
      (lcp1-address-p (lcp1-t1 address))
      (integerp (lcp1-t index))
      (integerp (lcp1-region base))))))

(defun lcp1-linked-p ()
  (if (lcp1-linked-op) t nil))

(defun lcp1-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lcp1-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (lcp1-address-base left)
     (lcp1-address-base right)))
   (<=
    (+ (lcp1-address-offset right) right-length)
    (lcp1-address-offset left))
   (<=
    (+ (lcp1-address-offset left) left-length)
    (lcp1-address-offset right))))

(defun lcp1-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lcp1-address-base address))
    (<= 0 (lcp1-address-offset address))
    (<=
     (+ (lcp1-address-offset address) length)
     (lcp1-t (lcp1-address-base address))))))

(defun-sk lcp1-framed-p ()
  (forall (address)
    (implies
     (lcp1-address-p address)
     (<=
      (lcp1-region
       (lcp1-address-base (lcp1-t1 address)))
      0))))

;; The updated memory is exactly Function.update t_1 a_1 (t_1 a).

(defun lcp1-pointer-read
    (memory-kind update-address update-value address)
  (if (and
       (equal memory-kind :updated)
       (equal address update-address))
      update-value
    (lcp1-t1 address)))

;; This recursion is equivalent to the source inductive p_linked_n relation:
;; n = 0 is exactly its bound constructor, while n > 0 is exactly its cons
;; constructor followed by the unique recursive predecessor at n - 1.

(defun lcp1-p-linked-n-p
    (memory-kind update-address update-value
                 root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (member-eq memory-kind '(:base :updated))
   (lcp1-address-p root)
   (lcp1-address-p array)
   (integerp index)
   (integerp n)
   (lcp1-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (lcp1-pointer-read
        memory-kind update-address update-value
        (lcp1-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (lcp1-valid-rw-p root 4)
      (lcp1-p-linked-n-p
       memory-kind update-address update-value
       (lcp1-pointer-read
        memory-kind update-address update-value
        (lcp1-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

(defun-sk lcp1-range-separated-p (a1 a2 i1 i)
  (forall (i2)
    (implies
     (and
      (integerp i2)
      (<= i1 i2)
      (< i2 (+ i i1)))
     (lcp1-separated-p
      a1 1
      (lcp1-t1 (lcp1-shift a2 i2))
      4))))

(defun-sk ntp4vc-list-copy-post-2-goal1-statement ()
  (forall
   (a2 a a1 i i1)
   (implies
    (and
     (lcp1-function-types-p)
     (lcp1-address-p a2)
     (lcp1-address-p a)
     (lcp1-address-p a1)
     (integerp i)
     (integerp i1))
    (let*
        ((a3 (lcp1-shift a2 0))
         (a4 (lcp1-t1 a)))
      (implies
       (and
        (<= (lcp1-region (lcp1-address-base a)) 0)
        (<= (lcp1-region (lcp1-address-base a1)) 0)
        (<= (lcp1-region (lcp1-address-base a2)) 0)
        (lcp1-framed-p)
        (lcp1-linked-p)
        (lcp1-is-sint32-p i)
        (lcp1-is-sint32-p i1)
        (lcp1-valid-rw-p a 1)
        (lcp1-valid-rw-p a1 1)
        (lcp1-valid-rw-p a3 2147483646)
        (lcp1-separated-p a1 1 a3 2147483646)
        (lcp1-separated-p
         (lcp1-t1 a1) 4 a3 2147483646)
        (lcp1-p-linked-n-p
         :base a1 a4
         a4 a2 i1 i (cons 0 0))
        (lcp1-range-separated-p a1 a2 i1 i))
       (lcp1-p-linked-n-p
        :updated a1 a4
        (lcp1-pointer-read :updated a1 a4 a)
        a2 i1 i (cons 0 0)))))))

(value-triple :itpeval-statement-checked)

:q
