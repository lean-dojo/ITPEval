;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_memb/memb_numfree_Why3_ide_VCmemb_numfree_post_goal0:
;; equality between the zero-valued memb-slot count up to the current index
;; and the memb_numfree count, under the stated memory-validity, framing,
;; range, and occurrence-bound hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun mn0-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun mn0-address-base (address)
  (car address))

(defun mn0-address-offset (address)
  (cdr address))

(defun mn0-shift (address amount)
  (cons
   (mn0-address-base address)
   (+ (mn0-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; pointer memory t_3, integer memories t_1 and t_2, allocation map t, region
;; function, and the linked and sconst predicates at the functions occurring
;; in this verification condition.

(defstub mn0-t3 (address) t)
(defstub mn0-t1 (address) t)
(defstub mn0-t2 (address) t)
(defstub mn0-allocation (index) t)
(defstub mn0-region (base) t)
(defstub mn0-linked-op () t)
(defstub mn0-sconst-op () t)

(defun-sk mn0-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (mn0-address-p address)
      (and
       (mn0-address-p (mn0-t3 address))
       (integerp (mn0-t1 address))
       (integerp (mn0-t2 address))))
     (implies
      (integerp index)
      (integerp (mn0-allocation index)))
     (implies
      (integerp base)
      (integerp (mn0-region base))))))

(defun mn0-linked-p ()
  (if (mn0-linked-op) t nil))

(defun mn0-sconst-p ()
  (if (mn0-sconst-op) t nil))

(defun mn0-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun mn0-is-uint16-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 65536)))

(defun mn0-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (mn0-address-base address))
    (<= 0 (mn0-address-offset address))
    (<=
     (+ (mn0-address-offset address) length)
     (mn0-allocation (mn0-address-base address))))))

(defun mn0-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (mn0-address-base address)))
    (<= 0 (mn0-address-offset address))
    (<=
     (+ (mn0-address-offset address) length)
     (mn0-allocation (mn0-address-base address))))))

(defun mn0-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (mn0-address-base left)
     (mn0-address-base right)))
   (<=
    (+ (mn0-address-offset right) right-length)
    (mn0-address-offset left))
   (<=
    (+ (mn0-address-offset left) left-length)
    (mn0-address-offset right))))

(defun-sk mn0-framed-p ()
  (forall (address)
    (implies
     (mn0-address-p address)
     (<=
      (mn0-region
       (mn0-address-base (mn0-t3 address)))
      0))))

;; Exact unfolding of Axiomatic13.p_valid_memb.

(defun mn0-p-valid-memb-p (m)
  (let*
      ((element-size
        (mn0-t1 (mn0-shift m 0)))
       (element-count
        (mn0-t1 (mn0-shift m 1)))
       (payload-size (* element-count element-size))
       (count-array
        (mn0-t3 (mn0-shift m 2)))
       (payload-array
        (mn0-t3 (mn0-shift m 3)))
       (count-start (mn0-shift count-array 0))
       (payload-start (mn0-shift payload-array 0)))
    (and
     (< 0 element-size)
     (<= payload-size 2147483647)
     (mn0-valid-rw-p m 4)
     (mn0-valid-rw-p count-array 1)
     (mn0-valid-rw-p payload-array 1)
     (mn0-valid-rw-p count-start element-count)
     (mn0-valid-rw-p payload-start payload-size)
     (mn0-separated-p
      count-start element-count payload-start payload-size))))

;; The source occurrence function is characterized by zero on empty intervals
;; and a one-step recurrence at the right endpoint. This terminating recursion
;; is the corresponding zero-valued slot count for t_2.

(defun mn0-occ-t2-aux (array from remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+
     (if
         (equal
          (mn0-t2
           (mn0-shift array (+ from (1- remaining))))
          0)
         1
       0)
     (mn0-occ-t2-aux array from (1- remaining)))))

(defun mn0-occ-t2 (array from to)
  (if
      (and
       (integerp from)
       (integerp to)
       (< from to))
      (mn0-occ-t2-aux array from (- to from))
    0))

;; Exact unfolding of Axiomatic13.l__memb_numfree for the fixed arbitrary
;; source memories.

(defun mn0-memb-numfree (m)
  (mn0-occ-t2
   (mn0-t3 (mn0-shift m 2))
   0
   (mn0-t1 (mn0-shift m 1))))

(defun-sk ntp4vc-memb-numfree-post-goal0-statement ()
  (forall
   (a i)
   (implies
    (and
     (mn0-function-types-p)
     (mn0-address-p a)
     (integerp i))
    (let*
        ((a1 (mn0-shift a 1))
         (x (mn0-t1 a1))
         (a2 (mn0-t3 (mn0-shift a 2)))
         (x1 (mn0-occ-t2 a2 0 i)))
      (implies
       (and
        (<= 0 i)
        (<= x i)
        (<= i x)
        (<= (mn0-region (mn0-address-base a)) 0)
        (<= x1 i)
        (mn0-framed-p)
        (mn0-linked-p)
        (mn0-sconst-p)
        (mn0-is-sint32-p i)
        (mn0-is-uint16-p x)
        (mn0-p-valid-memb-p a)
        (mn0-valid-rd-p a1 1)
        (mn0-is-sint32-p x1))
       (equal
        (mn0-occ-t2 a2 0 x)
        (mn0-memb-numfree a)))))))

(value-triple :itpeval-statement-checked)

:q
