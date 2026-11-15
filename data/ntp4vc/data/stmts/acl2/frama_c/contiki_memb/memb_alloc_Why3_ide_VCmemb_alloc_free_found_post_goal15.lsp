;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_memb/memb_alloc_Why3_ide_VCmemb_alloc_free_found_post_goal15:
;; existence of the selected free memb slot after updating its allocation
;; marker, with all other slots unchanged under the stated scan, memory,
;; framing, and integer-range hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun g15-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun g15-address-base (address)
  (car address))

(defun g15-address-offset (address)
  (cdr address))

(defun g15-shift (address amount)
  (cons
   (g15-address-base address)
   (+ (g15-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; pointer memory t_4, integer memories t_1, t_2, and t_3, allocation map t,
;; region function, and the linked and sconst predicates at the functions
;; appearing in this verification condition.

(defstub g15-t4 (address) t)
(defstub g15-t1 (address) t)
(defstub g15-t3 (address) t)
(defstub g15-allocation (index) t)
(defstub g15-t2 (address) t)
(defstub g15-region (base) t)
(defstub g15-linked-op () t)
(defstub g15-sconst-op () t)

(defun-sk g15-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (g15-address-p address)
      (and
       (g15-address-p (g15-t4 address))
       (integerp (g15-t1 address))
       (integerp (g15-t3 address))
       (integerp (g15-t2 address))))
     (implies
      (integerp index)
      (integerp (g15-allocation index)))
     (implies
      (integerp base)
      (integerp (g15-region base))))))

(defun g15-linked-p ()
  (if (g15-linked-op) t nil))

(defun g15-sconst-p ()
  (if (g15-sconst-op) t nil))

(defun g15-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun g15-is-uint16-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 65536)))

(defun g15-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (g15-address-base address))
    (<= 0 (g15-address-offset address))
    (<=
     (+ (g15-address-offset address) length)
     (g15-allocation (g15-address-base address))))))

(defun g15-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (g15-address-base address)))
    (<= 0 (g15-address-offset address))
    (<=
     (+ (g15-address-offset address) length)
     (g15-allocation (g15-address-base address))))))

(defun g15-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (g15-address-base left)
     (g15-address-base right)))
   (<=
    (+ (g15-address-offset right) right-length)
    (g15-address-offset left))
   (<=
    (+ (g15-address-offset left) left-length)
    (g15-address-offset right))))

(defun-sk g15-framed-p ()
  (forall (address)
    (implies
     (g15-address-p address)
     (<=
      (g15-region
       (g15-address-base (g15-t4 address)))
      0))))

;; This is the exact unfolding of Axiomatic13.p_valid_memb.

(defun g15-p-valid-memb-p (m)
  (let*
      ((element-size
        (g15-t1 (g15-shift m 0)))
       (element-count
        (g15-t1 (g15-shift m 1)))
       (payload-size (* element-count element-size))
       (count-array
        (g15-t4 (g15-shift m 2)))
       (payload-array
        (g15-t4 (g15-shift m 3)))
       (count-start (g15-shift count-array 0))
       (payload-start (g15-shift payload-array 0)))
    (and
     (< 0 element-size)
     (<= payload-size 2147483647)
     (g15-valid-rw-p m 4)
     (g15-valid-rw-p count-array 1)
     (g15-valid-rw-p payload-array 1)
     (g15-valid-rw-p count-start element-count)
     (g15-valid-rw-p payload-start payload-size)
     (g15-separated-p
      count-start element-count payload-start payload-size))))

;; Equality with Function.update is represented extensionally over the whole
;; source address domain: t_2 is t_3 updated to one at UPDATED-ADDRESS.

(defun-sk g15-updated-memory-p (updated-address)
  (forall (address)
    (implies
     (g15-address-p address)
     (equal
      (g15-t2 address)
      (if (equal address updated-address)
          1
        (g15-t3 address))))))

(defun-sk g15-unchanged-memory-p ()
  (forall (address)
    (implies
     (g15-address-p address)
     (equal (g15-t3 address) (g15-t2 address)))))

;; This preserves the source universal scan invariant over every integer below
;; i_1.

(defun-sk g15-earlier-slots-nonzero-p (array bound)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index bound))
     (not
      (equal
       (g15-t3 (g15-shift array index))
       0)))))

;; For a selected witness, every other slot in the two open subranges keeps
;; the same value in t_3 and t_2.

(defun-sk g15-other-slots-unchanged-p
    (array witness bound)
  (forall (index)
    (implies
     (and
      (integerp index)
      (or
       (and
        (<= 0 index)
        (< index witness))
       (and
        (< witness index)
        (< index bound))))
     (equal
      (g15-t3 (g15-shift array index))
      (g15-t2 (g15-shift array index))))))

;; The source conclusion keeps the selected index existentially quantified.

(defun-sk g15-postcondition-p
    (count-array payload-array count element-size result)
  (exists (index)
    (and
     (integerp index)
     (let ((slot (g15-shift count-array index)))
       (and
        (equal (g15-t2 slot) 1)
        (equal (g15-t3 slot) 0)
        (equal
         (g15-shift payload-array (* index element-size))
         result)
        (<= 0 index)
        (< index count)
        (g15-other-slots-unchanged-p
         count-array index count))))))

(defun-sk ntp4vc-memb-alloc-free-found-post-goal15-statement ()
  (forall
   (a1 i2 i i1 result)
   (implies
    (and
     (g15-function-types-p)
     (g15-address-p a1)
     (integerp i2)
     (integerp i)
     (integerp i1)
     (g15-address-p result))
    (let*
        ((a2 (g15-shift a1 2))
         (a3 (g15-t4 a2))
         (a4 (g15-shift a1 1))
         (x (g15-t1 a4))
         (a5 (g15-shift a1 0))
         (x1 (g15-t1 a5))
         (a6 (g15-shift a3 i2))
         (a7 (g15-shift a1 3))
         (a8 (g15-t4 a7))
         (x2 (* i2 x1)))
      (implies
       (and
        (equal (g15-t3 (g15-shift a3 i)) 0)
        (<= 0 i)
        (<= 0 i1)
        (< i x)
        (<= i1 x)
        (<= (g15-region (g15-address-base a1)) 0)
        (g15-framed-p)
        (g15-linked-p)
        (g15-sconst-p)
        (g15-is-sint32-p i1)
        (g15-is-sint32-p i2)
        (g15-is-uint16-p x)
        (g15-is-uint16-p x1)
        (g15-p-valid-memb-p a1)
        (g15-valid-rd-p a4 1)
        (if (< i1 x)
            (and
             (equal i2 i1)
             (equal (g15-t3 a6) 0)
             (g15-updated-memory-p a6)
             (equal (g15-shift a8 x2) result)
             (<= -2147483648 x2)
             (<= x2 2147483647)
             (g15-valid-rd-p a2 1)
             (g15-valid-rd-p a7 1)
             (g15-valid-rd-p a5 1)
             (g15-valid-rd-p a6 1)
             (g15-valid-rw-p a6 1))
          (and
           (g15-unchanged-memory-p)
           (equal (cons 0 0) result)))
        (g15-earlier-slots-nonzero-p a3 i1))
       (g15-postcondition-p a3 a8 x x1 result))))))

(value-triple :itpeval-statement-checked)

:q
