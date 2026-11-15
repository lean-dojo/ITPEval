;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/klibc_stdio/_fwrite_Why3_ide_VC_fwrite_call___fflush_pre_part1_goal15:
;; preservation of private I/O file validity after three successive
;; integer-memory updates under the stated framing, memory-validity,
;; file-structure, and 32-bit integer-range hypotheses. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun fw15-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun fw15-address-base (address)
  (car address))

(defun fw15-address-offset (address)
  (cdr address))

(defun fw15-shift (address amount)
  (cons
   (fw15-address-base address)
   (+ (fw15-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; integer memory t_1, pointer memory t_3, allocation map t, integer memory
;; t_2, region function, address-order relations, and the linked and sconst
;; predicates at t and t_2.

(defstub fw15-integer-memory (address) t)
(defstub fw15-pointer-memory (address) t)
(defstub fw15-allocation (index) t)
(defstub fw15-constant-memory (address) t)
(defstub fw15-region (base) t)
(defstub fw15-addr-le-op (left right) t)
(defstub fw15-addr-lt-op (left right) t)
(defstub fw15-linked-op () t)
(defstub fw15-sconst-op () t)

(defun-sk fw15-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (fw15-address-p address)
      (and
       (integerp (fw15-integer-memory address))
       (fw15-address-p (fw15-pointer-memory address))
       (integerp (fw15-constant-memory address))))
     (implies
      (integerp index)
      (integerp (fw15-allocation index)))
     (implies
      (integerp base)
      (integerp (fw15-region base))))))

(defun fw15-addr-le-p (left right)
  (if (fw15-addr-le-op left right) t nil))

(defun fw15-addr-lt-p (left right)
  (if (fw15-addr-lt-op left right) t nil))

;; These are the exact source laws for address order: for addresses with the
;; same base, address order is precisely integer order on offsets.

(defun-sk fw15-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (fw15-address-p left)
      (fw15-address-p right)
      (equal
       (fw15-address-base left)
       (fw15-address-base right)))
     (and
      (equal
       (fw15-addr-le-p left right)
       (<=
        (fw15-address-offset left)
        (fw15-address-offset right)))
      (equal
       (fw15-addr-lt-p left right)
       (<
        (fw15-address-offset left)
        (fw15-address-offset right)))))))

(defun fw15-linked-p ()
  (if (fw15-linked-op) t nil))

(defun fw15-sconst-p ()
  (if (fw15-sconst-op) t nil))

(defun fw15-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

;; Exact unfoldings of Memory.valid_rw and Memory.separated.

(defun fw15-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (fw15-address-base address))
    (<= 0 (fw15-address-offset address))
    (<=
     (+ (fw15-address-offset address) length)
     (fw15-allocation (fw15-address-base address))))))

(defun fw15-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (fw15-address-base left)
     (fw15-address-base right)))
   (<=
    (+ (fw15-address-offset right) right-length)
    (fw15-address-offset left))
   (<=
    (+ (fw15-address-offset left) left-length)
    (fw15-address-offset right))))

;; Exact unfolding of Memory.framed for the arbitrary pointer memory t_3.

(defun-sk fw15-framed-p ()
  (forall (address)
    (implies
     (fw15-address-p address)
     (<=
      (fw15-region
       (fw15-address-base (fw15-pointer-memory address)))
      0))))

;; An update list is newest first. Assoc-equal therefore implements exact
;; successive Function.update semantics, including every possible alias.

(defun fw15-integer-memory-read (updates address)
  (let ((entry (assoc-equal address updates)))
    (if entry
        (cdr entry)
      (fw15-integer-memory address))))

(defun fw15-integer-memory-write (updates address value)
  (cons (cons address value) updates))

;; Exact unfolding of Axiomatic3.p_valid_file for the selected integer-memory
;; update state.

(defun fw15-p-valid-file-p (updates file)
  (and
   (<=
    0
    (fw15-integer-memory-read
     updates
     (fw15-shift file 0)))
   (fw15-valid-rw-p file 3)))

;; Exact unfolding of Axiomatic3.p_valid_io_file_pvt_norec.

(defun fw15-p-valid-io-file-pvt-norec-p (updates file)
  (let*
      ((x
        (fw15-integer-memory-read
         updates
         (fw15-shift file 9)))
       (x1
        (fw15-integer-memory-read
         updates
         (fw15-shift file 7)))
       (x2
        (fw15-integer-memory-read
         updates
         (fw15-shift file 8)))
       (a
        (fw15-pointer-memory
         (fw15-shift file 5)))
       (a1
        (fw15-pointer-memory
         (fw15-shift file 6)))
       (a2
        (fw15-pointer-memory
         (fw15-shift file 4)))
       (a3
        (fw15-pointer-memory
         (fw15-shift file 3)))
       (a4 (fw15-shift a 0))
       (x3 (+ 32 x)))
    (and
     (equal x 16384)
     (<= 0 x1)
     (< x1 x)
     (<= 0 x2)
     (< x2 x)
     (fw15-valid-rw-p file 11)
     (fw15-addr-le-p a a1)
     (fw15-p-valid-file-p updates (fw15-shift file 0))
     (fw15-valid-rw-p a2 11)
     (fw15-valid-rw-p a3 11)
     (fw15-separated-p file 11 a2 11)
     (fw15-separated-p file 11 a3 11)
     (fw15-separated-p a2 11 a3 11)
     (fw15-valid-rw-p a4 x3)
     (fw15-separated-p file 11 a4 x3)
     (fw15-separated-p a2 11 a4 x3)
     (fw15-separated-p a3 11 a4 x3)
     (fw15-addr-lt-p a1 (fw15-shift a x3)))))

;; Exact unfolding of Axiomatic3.p_valid_io_file_pvt.

(defun fw15-p-valid-io-file-pvt-p (updates file)
  (let*
      ((x
        (fw15-integer-memory-read
         updates
         (fw15-shift file 9)))
       (a
        (fw15-pointer-memory
         (fw15-shift file 6)))
       (a1
        (fw15-pointer-memory
         (fw15-shift file 5)))
       (a2
        (fw15-pointer-memory
         (fw15-shift file 3)))
       (a3
        (fw15-pointer-memory
         (fw15-shift file 4)))
       (x1
        (fw15-integer-memory-read
         updates
         (fw15-shift file 7)))
       (x2
        (fw15-integer-memory-read
         updates
         (fw15-shift file 8)))
       (a4 (fw15-shift a1 0))
       (x3 (+ 32 x)))
    (and
     (equal x 16384)
     (equal
      (fw15-address-base a)
      (fw15-address-base a1))
     (equal
      (fw15-pointer-memory (fw15-shift a2 4))
      file)
     (equal
      (fw15-pointer-memory (fw15-shift a3 3))
      file)
     (<= 0 x1)
     (< x1 x)
     (<= 0 x2)
     (< x2 x)
     (fw15-valid-rw-p file 11)
     (fw15-addr-le-p a1 a)
     (fw15-p-valid-file-p updates (fw15-shift file 0))
     (fw15-separated-p file 11 a3 11)
     (fw15-separated-p file 11 a2 11)
     (fw15-separated-p a3 11 a2 11)
     (fw15-p-valid-io-file-pvt-norec-p updates a3)
     (fw15-p-valid-io-file-pvt-norec-p updates a2)
     (fw15-valid-rw-p a4 x3)
     (fw15-separated-p file 11 a4 x3)
     (fw15-separated-p a3 11 a4 x3)
     (fw15-separated-p a2 11 a4 x3)
     (fw15-addr-lt-p a (fw15-shift a1 x3)))))

(defun-sk ntp4vc-fwrite-fflush-pre-part1-goal15-statement ()
  (forall
   (a5 i3 a2 a i4 a4 a1 a3 i i1 i2)
   (implies
    (and
     (fw15-function-types-p)
     (fw15-address-order-laws-p)
     (fw15-address-p a5)
     (integerp i3)
     (fw15-address-p a2)
     (fw15-address-p a)
     (integerp i4)
     (fw15-address-p a4)
     (fw15-address-p a1)
     (fw15-address-p a3)
     (integerp i)
     (integerp i1)
     (integerp i2))
    (let*
        ((x
          (fw15-integer-memory-read
           nil
           (fw15-shift a5 10)))
         (data-pointer
          (fw15-pointer-memory
           (fw15-shift a5 6)))
         (buffer-pointer
          (fw15-pointer-memory
           (fw15-shift a5 5)))
         (previous-file
          (fw15-pointer-memory
           (fw15-shift a5 4)))
         (next-file
          (fw15-pointer-memory
           (fw15-shift a5 3)))
         (input-bytes
          (fw15-integer-memory-read
           nil
           (fw15-shift a5 7)))
         (buffer-start
          (fw15-shift buffer-pointer 0))
         (public-file (fw15-shift a5 0))
         (updated-integer-memory
          (fw15-integer-memory-write
           (fw15-integer-memory-write
            (fw15-integer-memory-write
             nil
             (fw15-shift a5 8)
             i)
            (fw15-shift public-file 1)
            i1)
           (fw15-shift public-file 2)
           i2)))
      (implies
       (and
        (not (equal i3 0))
        (equal
         (fw15-shift a2 0)
         (fw15-shift a 0))
        (not (equal x 1))
        (not (equal x 2))
        (equal
         (fw15-integer-memory-read
          nil
          (fw15-shift a5 9))
         16384)
        (equal
         (fw15-address-base data-pointer)
         (fw15-address-base buffer-pointer))
        (equal
         (fw15-pointer-memory
          (fw15-shift previous-file 3))
         a5)
        (equal
         (fw15-pointer-memory
          (fw15-shift next-file 4))
         a5)
        (<= 0 i)
        (<= 0 i3)
        (<= 0 i4)
        (<= 0 input-bytes)
        (<= (fw15-region (fw15-address-base a2)) 0)
        (<= (fw15-region (fw15-address-base a4)) 0)
        (<= i 16383)
        (<= input-bytes 16383)
        (fw15-framed-p)
        (fw15-linked-p)
        (fw15-sconst-p)
        (fw15-is-uint32-p i)
        (fw15-is-uint32-p i3)
        (fw15-is-uint32-p i4)
        (fw15-valid-rw-p a5 11)
        (fw15-is-uint32-p x)
        (fw15-is-uint32-p input-bytes)
        (fw15-p-valid-io-file-pvt-p nil a1)
        (fw15-p-valid-io-file-pvt-p nil a3)
        (fw15-p-valid-io-file-pvt-p nil a5)
        (fw15-addr-le-p buffer-pointer data-pointer)
        (fw15-valid-rw-p (fw15-shift a4 0) i3)
        (fw15-separated-p a5 11 next-file 11)
        (fw15-separated-p a5 11 previous-file 11)
        (fw15-separated-p next-file 11 previous-file 11)
        (fw15-addr-lt-p
         data-pointer
         (fw15-shift buffer-pointer 16416))
        (fw15-valid-rw-p buffer-start 16416)
        (fw15-p-valid-file-p
         updated-integer-memory
         public-file)
        (fw15-separated-p a5 11 buffer-start 16416)
        (fw15-separated-p next-file 11 buffer-start 16416)
        (fw15-separated-p previous-file 11 buffer-start 16416)
        (fw15-p-valid-io-file-pvt-norec-p
         updated-integer-memory
         next-file)
        (fw15-p-valid-io-file-pvt-norec-p
         updated-integer-memory
         previous-file))
       (fw15-p-valid-io-file-pvt-p
        updated-integer-memory
        a5))))))

(value-triple :itpeval-statement-checked)

:q
