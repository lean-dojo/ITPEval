;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/klibc_stdio/__fflush_Why3_ide_VC__fflush_call_write_pre_goal31:
;; nonnegativity of the file-buffer integer read before the write call under
;; the stated address-order, framing, memory-validity, file-structure, and
;; 32-bit integer-range hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun ff31-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun ff31-address-base (address)
  (car address))

(defun ff31-address-offset (address)
  (cdr address))

(defun ff31-shift (address amount)
  (cons
   (ff31-address-base address)
   (+ (ff31-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; pointer memory t_2, integer memory t_1, allocation map t, region function,
;; address-order relations, and the linked predicate at t.

(defstub ff31-t2 (address) t)
(defstub ff31-t1 (address) t)
(defstub ff31-allocation (index) t)
(defstub ff31-region (base) t)
(defstub ff31-addr-le-op (left right) t)
(defstub ff31-addr-lt-op (left right) t)
(defstub ff31-linked-op () t)

(defun-sk ff31-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (ff31-address-p address)
      (and
       (ff31-address-p (ff31-t2 address))
       (integerp (ff31-t1 address))))
     (implies
      (integerp index)
      (integerp (ff31-allocation index)))
     (implies
      (integerp base)
      (integerp (ff31-region base))))))

(defun ff31-addr-le-p (left right)
  (if (ff31-addr-le-op left right) t nil))

(defun ff31-addr-lt-p (left right)
  (if (ff31-addr-lt-op left right) t nil))

;; These are the exact source laws for address order: when two addresses have
;; the same base, their order is precisely the integer order of their offsets.

(defun-sk ff31-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (ff31-address-p left)
      (ff31-address-p right)
      (equal
       (ff31-address-base left)
       (ff31-address-base right)))
     (and
      (equal
       (ff31-addr-le-p left right)
       (<=
        (ff31-address-offset left)
        (ff31-address-offset right)))
      (equal
       (ff31-addr-lt-p left right)
       (<
        (ff31-address-offset left)
        (ff31-address-offset right)))))))

(defun ff31-linked-p ()
  (if (ff31-linked-op) t nil))

(defun ff31-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun ff31-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

;; Exact unfoldings of Memory.valid_rw and Memory.separated.

(defun ff31-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (ff31-address-base address))
    (<= 0 (ff31-address-offset address))
    (<=
     (+ (ff31-address-offset address) length)
     (ff31-allocation (ff31-address-base address))))))

(defun ff31-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (ff31-address-base left)
     (ff31-address-base right)))
   (<=
    (+ (ff31-address-offset right) right-length)
    (ff31-address-offset left))
   (<=
    (+ (ff31-address-offset left) left-length)
    (ff31-address-offset right))))

;; Exact unfolding of Memory.framed for the arbitrary pointer memory t_2.

(defun-sk ff31-framed-p ()
  (forall (address)
    (implies
     (ff31-address-p address)
     (<=
      (ff31-region
       (ff31-address-base (ff31-t2 address)))
      0))))

;; Exact unfolding of Axiomatic3.p_valid_file.

(defun ff31-p-valid-file-p (file)
  (and
   (<= 0 (ff31-t1 (ff31-shift file 0)))
   (ff31-valid-rw-p file 3)))

;; Exact unfolding of Axiomatic3.p_valid_io_file_pvt_norec.

(defun ff31-p-valid-io-file-pvt-norec-p (file)
  (let*
      ((x (ff31-t1 (ff31-shift file 9)))
       (x1 (ff31-t1 (ff31-shift file 7)))
       (x2 (ff31-t1 (ff31-shift file 8)))
       (a (ff31-t2 (ff31-shift file 5)))
       (a1 (ff31-t2 (ff31-shift file 6)))
       (a2 (ff31-t2 (ff31-shift file 4)))
       (a3 (ff31-t2 (ff31-shift file 3)))
       (a4 (ff31-shift a 0))
       (x3 (+ 32 x)))
    (and
     (equal x 16384)
     (<= 0 x1)
     (< x1 x)
     (<= 0 x2)
     (< x2 x)
     (ff31-valid-rw-p file 11)
     (ff31-addr-le-p a a1)
     (ff31-p-valid-file-p (ff31-shift file 0))
     (ff31-valid-rw-p a2 11)
     (ff31-valid-rw-p a3 11)
     (ff31-separated-p file 11 a2 11)
     (ff31-separated-p file 11 a3 11)
     (ff31-separated-p a2 11 a3 11)
     (ff31-valid-rw-p a4 x3)
     (ff31-separated-p file 11 a4 x3)
     (ff31-separated-p a2 11 a4 x3)
     (ff31-separated-p a3 11 a4 x3)
     (ff31-addr-lt-p a1 (ff31-shift a x3)))))

;; Exact unfolding of Axiomatic3.p_valid_io_file_pvt.

(defun ff31-p-valid-io-file-pvt-p (file)
  (let*
      ((x (ff31-t1 (ff31-shift file 9)))
       (a (ff31-t2 (ff31-shift file 6)))
       (a1 (ff31-t2 (ff31-shift file 5)))
       (a2 (ff31-t2 (ff31-shift file 3)))
       (a3 (ff31-t2 (ff31-shift file 4)))
       (x1 (ff31-t1 (ff31-shift file 7)))
       (x2 (ff31-t1 (ff31-shift file 8)))
       (a4 (ff31-shift a1 0))
       (x3 (+ 32 x)))
    (and
     (equal x 16384)
     (equal
      (ff31-address-base a)
      (ff31-address-base a1))
     (equal
      (ff31-t2 (ff31-shift a2 4))
      file)
     (equal
      (ff31-t2 (ff31-shift a3 3))
      file)
     (<= 0 x1)
     (< x1 x)
     (<= 0 x2)
     (< x2 x)
     (ff31-valid-rw-p file 11)
     (ff31-addr-le-p a1 a)
     (ff31-p-valid-file-p (ff31-shift file 0))
     (ff31-separated-p file 11 a3 11)
     (ff31-separated-p file 11 a2 11)
     (ff31-separated-p a3 11 a2 11)
     (ff31-p-valid-io-file-pvt-norec-p a3)
     (ff31-p-valid-io-file-pvt-norec-p a2)
     (ff31-valid-rw-p a4 x3)
     (ff31-separated-p file 11 a4 x3)
     (ff31-separated-p a3 11 a4 x3)
     (ff31-separated-p a2 11 a4 x3)
     (ff31-addr-lt-p a (ff31-shift a1 x3)))))

(defun-sk
    ntp4vc-fflush-call-write-pre-goal31-statement ()
  (forall
   (a1 a i i1)
   (implies
    (and
     (ff31-function-types-p)
     (ff31-address-order-laws-p)
     (ff31-address-p a1)
     (ff31-address-p a)
     (integerp i)
     (integerp i1))
    (let*
        ((a2 (ff31-t2 (ff31-shift a1 5)))
         (x (ff31-address-base a2))
         (x1 (ff31-address-base a))
         (x2
          (ff31-address-base
           (ff31-t2 (ff31-shift a1 6))))
         (x3 (ff31-t1 (ff31-shift a1 9)))
         (x4
          (ff31-t1
           (ff31-shift
            (ff31-shift a1 0)
            0))))
      (implies
       (and
        (not (equal i 0))
        (equal (ff31-t1 (ff31-shift a1 7)) 0)
        (equal x x1)
        (equal x2 x1)
        (equal x2 x)
        (<= 0 i)
        (<= i1 i)
        (<= (ff31-region (ff31-address-base a1)) 0)
        (<= -1 i1)
        (ff31-framed-p)
        (ff31-linked-p)
        (ff31-is-uint32-p i)
        (ff31-is-sint32-p i1)
        (ff31-is-uint32-p x3)
        (ff31-is-uint32-p
         (ff31-t1 (ff31-shift a1 8)))
        (ff31-p-valid-io-file-pvt-p a1)
        (ff31-addr-le-p a2 a)
        (ff31-valid-rw-p (ff31-shift a 0) i)
        (ff31-is-sint32-p x4)
        (ff31-addr-le-p
         a
         (ff31-shift a2 (+ 32 x3))))
       (<= 0 x4))))))

(value-triple :itpeval-statement-checked)

:q
