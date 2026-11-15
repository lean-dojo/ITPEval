;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/linked_n_merge_segment_Why3_ide_VClinked_n_merge_segment_loop_inv_3_preserved_goal8:
;; preservation of an inductively defined linked-list segment invariant while
;; merging adjacent list segments. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lnmsg8-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lnmsg8-address-base (address)
  (car address))

(defun lnmsg8-address-offset (address)
  (cdr address))

(defun lnmsg8-shift (address amount)
  (cons
   (lnmsg8-address-base address)
   (+ (lnmsg8-address-offset address) amount)))

;; These conservative symbols represent the universally arbitrary source
;; pointer function t_1, integer function t, region operation, and the linked
;; proposition specialized to t.

(defstub lnmsg8-t1 (address) t)
(defstub lnmsg8-t (index) t)
(defstub lnmsg8-region (base) t)
(defstub lnmsg8-linked-op () t)

(defun-sk lnmsg8-function-types-p ()
  (forall (address index base)
    (implies
     (and
      (lnmsg8-address-p address)
      (integerp index)
      (integerp base))
     (and
      (lnmsg8-address-p (lnmsg8-t1 address))
      (integerp (lnmsg8-t index))
      (integerp (lnmsg8-region base))))))

(defun lnmsg8-linked-p ()
  (if (lnmsg8-linked-op) t nil))

(defun lnmsg8-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lnmsg8-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lnmsg8-address-base address))
    (<= 0 (lnmsg8-address-offset address))
    (<=
     (+ (lnmsg8-address-offset address) length)
     (lnmsg8-t (lnmsg8-address-base address))))))

;; This recursion is equivalent to the source inductive p_linked_n relation:
;; n = 0 is exactly its bound constructor, while n > 0 is exactly its cons
;; constructor followed by the unique recursive predecessor at n - 1.

(defun lnmsg8-p-linked-n-p (root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (lnmsg8-address-p root)
   (lnmsg8-address-p array)
   (integerp index)
   (integerp n)
   (lnmsg8-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (lnmsg8-t1 (lnmsg8-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (lnmsg8-valid-rw-p root 4)
      (lnmsg8-p-linked-n-p
       (lnmsg8-t1 (lnmsg8-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

(defun-sk lnmsg8-framed-p ()
  (forall (address)
    (implies
     (lnmsg8-address-p address)
     (<=
      (lnmsg8-region
       (lnmsg8-address-base (lnmsg8-t1 address)))
      0))))

(defun-sk
    ntp4vc-linked-n-merge-segment-loop-inv-3-preserved-goal8-statement ()
  (forall
   (i3 a3 i1 i2 i a a1 a2)
   (implies
    (and
     (lnmsg8-function-types-p)
     (integerp i3)
     (lnmsg8-address-p a3)
     (integerp i1)
     (integerp i2)
     (integerp i)
     (lnmsg8-address-p a)
     (lnmsg8-address-p a1)
     (lnmsg8-address-p a2))
    (let*
        ((x (- i3 1))
         (a4
          (lnmsg8-t1
           (lnmsg8-shift
            (lnmsg8-t1
             (lnmsg8-shift a3 (- (+ i1 i3) 1)))
            0))))
      (implies
       (and
        (not (equal i2 0))
        (< 0 i3)
        (<= 0 i)
        (<= 0 i2)
        (<= i3 i2)
        (<= (lnmsg8-region (lnmsg8-address-base a)) 0)
        (<= (lnmsg8-region (lnmsg8-address-base a1)) 0)
        (<= (lnmsg8-region (lnmsg8-address-base a2)) 0)
        (<= (lnmsg8-region (lnmsg8-address-base a3)) 0)
        (<= 2 i3)
        (lnmsg8-framed-p)
        (lnmsg8-linked-p)
        (lnmsg8-is-sint32-p i)
        (lnmsg8-is-sint32-p i1)
        (lnmsg8-is-sint32-p i2)
        (lnmsg8-is-sint32-p i3)
        (lnmsg8-is-sint32-p x)
        (lnmsg8-valid-rw-p
         (lnmsg8-shift a3 0)
         2147483646)
        (lnmsg8-p-linked-n-p
         a a3 i1 i2 a2)
        (lnmsg8-p-linked-n-p
         a2 a3 (+ i1 i2) i a1)
        (lnmsg8-p-linked-n-p
         a a3 i1 i3 a4)
        (lnmsg8-p-linked-n-p
         a4 a3 (+ i1 i3) (- (+ i i2) i3) a1))
       (lnmsg8-p-linked-n-p
        a
        a3
        i1
        x
        (lnmsg8-t1
         (lnmsg8-shift
          (lnmsg8-t1
           (lnmsg8-shift a3 (- (+ i1 i3) 2)))
          0))))))))

(value-triple :itpeval-statement-checked)

:q
