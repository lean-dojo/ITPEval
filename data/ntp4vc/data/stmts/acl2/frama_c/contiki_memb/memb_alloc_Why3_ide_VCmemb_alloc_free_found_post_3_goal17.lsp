;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_memb/memb_alloc_Why3_ide_VCmemb_alloc_free_found_post_3_goal17:
;; updating the first selected zero-valued memb slot to one decreases the
;; number of zero-valued slots by exactly one under the stated memory,
;; framing, range, and scan hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun g17-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun g17-address-base (address)
  (car address))

(defun g17-address-offset (address)
  (cdr address))

(defun g17-shift (address amount)
  (cons
   (g17-address-base address)
   (+ (g17-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; pointer memory t_4, integer memories t_1, t_2, and t_3, allocation map t,
;; region function, and the linked and sconst predicates at the functions
;; appearing in this verification condition.

(defstub g17-t4 (address) t)
(defstub g17-t1 (address) t)
(defstub g17-t2 (address) t)
(defstub g17-allocation (index) t)
(defstub g17-t3 (address) t)
(defstub g17-region (base) t)
(defstub g17-linked-op () t)
(defstub g17-sconst-op () t)

(defun-sk g17-function-types-p ()
  (forall (address index base)
    (implies
     (and
      (g17-address-p address)
      (integerp index)
      (integerp base))
     (and
      (g17-address-p (g17-t4 address))
      (integerp (g17-t1 address))
      (integerp (g17-t2 address))
      (integerp (g17-allocation index))
      (integerp (g17-t3 address))
      (integerp (g17-region base))))))

(defun g17-linked-p ()
  (if (g17-linked-op) t nil))

(defun g17-sconst-p ()
  (if (g17-sconst-op) t nil))

(defun g17-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun g17-is-uint16-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 65536)))

(defun g17-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (g17-address-base address))
    (<= 0 (g17-address-offset address))
    (<=
     (+ (g17-address-offset address) length)
     (g17-allocation (g17-address-base address))))))

(defun g17-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (g17-address-base address)))
    (<= 0 (g17-address-offset address))
    (<=
     (+ (g17-address-offset address) length)
     (g17-allocation (g17-address-base address))))))

(defun g17-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (g17-address-base left)
     (g17-address-base right)))
   (<=
    (+ (g17-address-offset right) right-length)
    (g17-address-offset left))
   (<=
    (+ (g17-address-offset left) left-length)
    (g17-address-offset right))))

(defun-sk g17-framed-p ()
  (forall (address)
    (implies
     (g17-address-p address)
     (<=
      (g17-region
       (g17-address-base (g17-t4 address)))
      0))))

;; This is the exact unfolding of Axiomatic13.p_valid_memb.

(defun g17-p-valid-memb-p (m)
  (let*
      ((element-size
        (g17-t1 (g17-shift m 0)))
       (element-count
        (g17-t1 (g17-shift m 1)))
       (payload-size (* element-count element-size))
       (count-array
        (g17-t4 (g17-shift m 2)))
       (payload-array
        (g17-t4 (g17-shift m 3)))
       (count-start (g17-shift count-array 0))
       (payload-start (g17-shift payload-array 0)))
    (and
     (< 0 element-size)
     (<= payload-size 2147483647)
     (g17-valid-rw-p m 4)
     (g17-valid-rw-p count-array 1)
     (g17-valid-rw-p payload-array 1)
     (g17-valid-rw-p count-start element-count)
     (g17-valid-rw-p payload-start payload-size)
     (g17-separated-p
      count-start element-count payload-start payload-size))))

;; Equality with Function.update is represented extensionally over the whole
;; source address domain.

(defun-sk g17-updated-memory-p (updated-address)
  (forall (address)
    (implies
     (g17-address-p address)
     (equal
      (g17-t3 address)
      (if (equal address updated-address)
          1
        (g17-t2 address))))))

(defun-sk g17-unchanged-memory-p ()
  (forall (address)
    (implies
     (g17-address-p address)
     (equal (g17-t3 address) (g17-t2 address)))))

;; This preserves the source universal scan invariant over every integer i_3.

(defun-sk g17-earlier-slots-nonzero-p (array bound)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index bound))
     (not
      (equal
       (g17-t2 (g17-shift array index))
       0)))))

;; The source occurrence function is characterized by zero on empty intervals
;; and a one-step recurrence at the right endpoint. These two terminating
;; recursions are that unique count for t_2 and t_3 respectively.

(defun g17-occ-t2-aux (array from remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+
     (if
         (equal
          (g17-t2
           (g17-shift array (+ from (1- remaining))))
          0)
         1
       0)
     (g17-occ-t2-aux array from (1- remaining)))))

(defun g17-occ-t3-aux (array from remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (+
     (if
         (equal
          (g17-t3
           (g17-shift array (+ from (1- remaining))))
          0)
         1
       0)
     (g17-occ-t3-aux array from (1- remaining)))))

(defun g17-occ-t2 (array from to)
  (if
      (and
       (integerp from)
       (integerp to)
       (< from to))
      (g17-occ-t2-aux array from (- to from))
    0))

(defun g17-occ-t3 (array from to)
  (if
      (and
       (integerp from)
       (integerp to)
       (< from to))
      (g17-occ-t3-aux array from (- to from))
    0))

(defun g17-numfree-t2 (m)
  (g17-occ-t2
   (g17-t4 (g17-shift m 2))
   0
   (g17-t1 (g17-shift m 1))))

(defun g17-numfree-t3 (m)
  (g17-occ-t3
   (g17-t4 (g17-shift m 2))
   0
   (g17-t1 (g17-shift m 1))))

(defun-sk
    ntp4vc-memb-alloc-free-found-post-3-goal17-statement ()
  (forall
   (a i2 i i1)
   (implies
    (and
     (g17-function-types-p)
     (g17-address-p a)
     (integerp i2)
     (integerp i)
     (integerp i1))
    (let*
        ((a1 (g17-shift a 2))
         (a2 (g17-t4 a1))
         (a3 (g17-shift a 1))
         (x (g17-t1 a3))
         (a4 (g17-shift a 0))
         (x1 (g17-t1 a4))
         (a5 (g17-shift a2 i2))
         (x2 (* i2 x1)))
      (implies
       (and
        (equal (g17-t2 (g17-shift a2 i)) 0)
        (<= 0 i)
        (<= 0 i1)
        (< i x)
        (<= i1 x)
        (<= (g17-region (g17-address-base a)) 0)
        (g17-framed-p)
        (g17-linked-p)
        (g17-sconst-p)
        (g17-is-sint32-p i1)
        (g17-is-sint32-p i2)
        (g17-is-uint16-p x)
        (g17-is-uint16-p x1)
        (g17-p-valid-memb-p a)
        (g17-valid-rd-p a3 1)
        (if (< i1 x)
            (and
             (equal i2 i1)
             (equal (g17-t2 a5) 0)
             (g17-updated-memory-p a5)
             (<= -2147483648 x2)
             (<= x2 2147483647)
             (g17-valid-rd-p a1 1)
             (g17-valid-rd-p (g17-shift a 3) 1)
             (g17-valid-rd-p a4 1)
             (g17-valid-rd-p a5 1)
             (g17-valid-rw-p a5 1))
          (g17-unchanged-memory-p))
        (g17-earlier-slots-nonzero-p a2 i1))
       (equal
        (+ 1 (g17-numfree-t3 a))
        (g17-numfree-t2 a)))))))

(value-triple :itpeval-statement-checked)

:q
