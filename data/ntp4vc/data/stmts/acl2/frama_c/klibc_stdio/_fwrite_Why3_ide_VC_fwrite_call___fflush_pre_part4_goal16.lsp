;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/klibc_stdio/_fwrite_Why3_ide_VC_fwrite_call___fflush_pre_part4_goal16:
;; preservation of private I/O file validity after three successive
;; integer-memory updates under the stated nonzero-length, marker-value,
;; interval-exclusion, framing, memory-validity, file-structure, and
;; 32-bit unsigned-integer hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun fw16-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun fw16-address-base (address)
  (car address))

(defun fw16-address-offset (address)
  (cdr address))

(defun fw16-shift (address amount)
  (cons
   (fw16-address-base address)
   (+ (fw16-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; integer memory t_1, pointer memory t_3, allocation map t, integer memory
;; t_2, region function, address-order relations, and the linked and sconst
;; predicates at t and t_2.

(defstub fw16-integer-memory (address) t)
(defstub fw16-pointer-memory (address) t)
(defstub fw16-allocation (index) t)
(defstub fw16-constant-memory (address) t)
(defstub fw16-region (base) t)
(defstub fw16-addr-le-op (left right) t)
(defstub fw16-addr-lt-op (left right) t)
(defstub fw16-linked-op () t)
(defstub fw16-sconst-op () t)

(defun-sk fw16-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (fw16-address-p address)
      (and
       (integerp (fw16-integer-memory address))
       (fw16-address-p (fw16-pointer-memory address))
       (integerp (fw16-constant-memory address))))
     (implies
      (integerp index)
      (integerp (fw16-allocation index)))
     (implies
      (integerp base)
      (integerp (fw16-region base))))))

(defun fw16-addr-le-p (left right)
  (if (fw16-addr-le-op left right) t nil))

(defun fw16-addr-lt-p (left right)
  (if (fw16-addr-lt-op left right) t nil))

;; These are the exact source laws for address order: for addresses with the
;; same base, address order is precisely integer order on offsets.

(defun-sk fw16-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (fw16-address-p left)
      (fw16-address-p right)
      (equal
       (fw16-address-base left)
       (fw16-address-base right)))
     (and
      (equal
       (fw16-addr-le-p left right)
       (<=
        (fw16-address-offset left)
        (fw16-address-offset right)))
      (equal
       (fw16-addr-lt-p left right)
       (<
        (fw16-address-offset left)
        (fw16-address-offset right)))))))

(defun fw16-linked-p ()
  (if (fw16-linked-op) t nil))

(defun fw16-sconst-p ()
  (if (fw16-sconst-op) t nil))

(defun fw16-is-uint32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

;; Exact unfoldings of Memory.valid_rw and Memory.separated.

(defun fw16-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (fw16-address-base address))
    (<= 0 (fw16-address-offset address))
    (<=
     (+ (fw16-address-offset address) length)
     (fw16-allocation (fw16-address-base address))))))

(defun fw16-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (fw16-address-base left)
     (fw16-address-base right)))
   (<=
    (+ (fw16-address-offset right) right-length)
    (fw16-address-offset left))
   (<=
    (+ (fw16-address-offset left) left-length)
    (fw16-address-offset right))))

;; Exact unfolding of Memory.framed for the arbitrary pointer memory t_3.

(defun-sk fw16-framed-p ()
  (forall (address)
    (implies
     (fw16-address-p address)
     (<=
      (fw16-region
       (fw16-address-base (fw16-pointer-memory address)))
      0))))

;; An update list is newest first. Assoc-equal therefore implements exact
;; successive Function.update semantics, including every possible alias.

(defun fw16-integer-memory-read (updates address)
  (let ((entry (assoc-equal address updates)))
    (if entry
        (cdr entry)
      (fw16-integer-memory address))))

(defun fw16-integer-memory-write (updates address value)
  (cons (cons address value) updates))

;; Exact unfolding of Axiomatic3.p_valid_file for the selected integer-memory
;; update state.

(defun fw16-p-valid-file-p (updates file)
  (and
   (<=
    0
    (fw16-integer-memory-read
     updates
     (fw16-shift file 0)))
   (fw16-valid-rw-p file 3)))

;; Exact unfolding of Axiomatic3.p_valid_io_file_pvt_norec.

(defun fw16-p-valid-io-file-pvt-norec-p (updates file)
  (let*
      ((x
        (fw16-integer-memory-read
         updates
         (fw16-shift file 9)))
       (x1
        (fw16-integer-memory-read
         updates
         (fw16-shift file 7)))
       (x2
        (fw16-integer-memory-read
         updates
         (fw16-shift file 8)))
       (a
        (fw16-pointer-memory
         (fw16-shift file 5)))
       (a1
        (fw16-pointer-memory
         (fw16-shift file 6)))
       (a2
        (fw16-pointer-memory
         (fw16-shift file 4)))
       (a3
        (fw16-pointer-memory
         (fw16-shift file 3)))
       (a4 (fw16-shift a 0))
       (x3 (+ 32 x)))
    (and
     (equal x 16384)
     (<= 0 x1)
     (< x1 x)
     (<= 0 x2)
     (< x2 x)
     (fw16-valid-rw-p file 11)
     (fw16-addr-le-p a a1)
     (fw16-p-valid-file-p updates (fw16-shift file 0))
     (fw16-valid-rw-p a2 11)
     (fw16-valid-rw-p a3 11)
     (fw16-separated-p file 11 a2 11)
     (fw16-separated-p file 11 a3 11)
     (fw16-separated-p a2 11 a3 11)
     (fw16-valid-rw-p a4 x3)
     (fw16-separated-p file 11 a4 x3)
     (fw16-separated-p a2 11 a4 x3)
     (fw16-separated-p a3 11 a4 x3)
     (fw16-addr-lt-p a1 (fw16-shift a x3)))))

;; Exact unfolding of Axiomatic3.p_valid_io_file_pvt.

(defun fw16-p-valid-io-file-pvt-p (updates file)
  (let*
      ((x
        (fw16-integer-memory-read
         updates
         (fw16-shift file 9)))
       (a
        (fw16-pointer-memory
         (fw16-shift file 6)))
       (a1
        (fw16-pointer-memory
         (fw16-shift file 5)))
       (a2
        (fw16-pointer-memory
         (fw16-shift file 3)))
       (a3
        (fw16-pointer-memory
         (fw16-shift file 4)))
       (x1
        (fw16-integer-memory-read
         updates
         (fw16-shift file 7)))
       (x2
        (fw16-integer-memory-read
         updates
         (fw16-shift file 8)))
       (a4 (fw16-shift a1 0))
       (x3 (+ 32 x)))
    (and
     (equal x 16384)
     (equal
      (fw16-address-base a)
      (fw16-address-base a1))
     (equal
      (fw16-pointer-memory (fw16-shift a2 4))
      file)
     (equal
      (fw16-pointer-memory (fw16-shift a3 3))
      file)
     (<= 0 x1)
     (< x1 x)
     (<= 0 x2)
     (< x2 x)
     (fw16-valid-rw-p file 11)
     (fw16-addr-le-p a1 a)
     (fw16-p-valid-file-p updates (fw16-shift file 0))
     (fw16-separated-p file 11 a3 11)
     (fw16-separated-p file 11 a2 11)
     (fw16-separated-p a3 11 a2 11)
     (fw16-p-valid-io-file-pvt-norec-p updates a3)
     (fw16-p-valid-io-file-pvt-norec-p updates a2)
     (fw16-valid-rw-p a4 x3)
     (fw16-separated-p file 11 a4 x3)
     (fw16-separated-p a3 11 a4 x3)
     (fw16-separated-p a2 11 a4 x3)
     (fw16-addr-lt-p a (fw16-shift a1 x3)))))

;; This is the source's integer-quantified interval-exclusion hypothesis.

(defun-sk fw16-interval-exclusion-p (i4 x a4)
  (forall (i6)
    (implies
     (integerp i6)
     (implies
      (and
       (< i4 i6)
       (<= i6 x))
      (not
       (equal
        (fw16-constant-memory
         (fw16-shift a4 (- i6 1)))
        10))))))

(defun-sk ntp4vc-fwrite-fflush-pre-part4-goal16-statement ()
  (forall
   (i3 i4 a4 a5 a2 a i5 a1 a3 i i1 i2)
   (implies
    (and
     (integerp i3)
     (integerp i4)
     (fw16-address-p a4)
     (fw16-address-p a5)
     (fw16-address-p a2)
     (fw16-address-p a)
     (integerp i5)
     (fw16-address-p a1)
     (fw16-address-p a3)
     (integerp i)
     (integerp i1)
     (integerp i2)
     (fw16-function-types-p)
     (fw16-address-order-laws-p))
    (let*
        ((x (+ i3 i4))
         (data-pointer
          (fw16-pointer-memory
           (fw16-shift a5 6)))
         (buffer-pointer
          (fw16-pointer-memory
           (fw16-shift a5 5)))
         (previous-file
          (fw16-pointer-memory
           (fw16-shift a5 4)))
         (next-file
          (fw16-pointer-memory
           (fw16-shift a5 3)))
         (input-bytes
          (fw16-integer-memory-read
           nil
           (fw16-shift a5 7)))
         (write-start (fw16-shift a4 0))
         (buffer-start
          (fw16-shift buffer-pointer 0))
         (public-file (fw16-shift a5 0))
         (updated-integer-memory
          (fw16-integer-memory-write
           (fw16-integer-memory-write
            (fw16-integer-memory-write
             nil
             (fw16-shift a5 8)
             i)
            (fw16-shift public-file 1)
            i1)
           (fw16-shift public-file 2)
           i2)))
      (implies
       (and
        (not (equal i4 0))
        (equal
         (fw16-shift a2 0)
         (fw16-shift a 0))
        (equal
         (fw16-integer-memory
          (fw16-shift a5 10))
         1)
        (equal
         (fw16-integer-memory
          (fw16-shift a5 9))
         16384)
        (equal
         (fw16-address-base data-pointer)
         (fw16-address-base buffer-pointer))
        (equal
         (fw16-pointer-memory
          (fw16-shift previous-file 3))
         a5)
        (equal
         (fw16-pointer-memory
          (fw16-shift next-file 4))
         a5)
        ;; Since i4 is a nonzero uint32, i4 - 1 is itself uint32. The source
        ;; id_uint32 law therefore makes to_uint32(i4 - 1) equal to i4 - 1.
        (equal
         (fw16-constant-memory
          (fw16-shift a4 (- i4 1)))
         10)
        (<= 0 i)
        (<= 0 i3)
        (<= 0 i4)
        (<= 0 i5)
        (<= 0 x)
        (<= 0 input-bytes)
        (<= (fw16-region (fw16-address-base a2)) 0)
        (<= (fw16-region (fw16-address-base a4)) 0)
        (<= i 16383)
        (<= input-bytes 16383)
        (fw16-framed-p)
        (fw16-linked-p)
        (fw16-sconst-p)
        (fw16-is-uint32-p i)
        (fw16-is-uint32-p i3)
        (fw16-is-uint32-p i4)
        (fw16-is-uint32-p i5)
        (fw16-valid-rw-p a5 11)
        (fw16-is-uint32-p x)
        (fw16-is-uint32-p input-bytes)
        (fw16-p-valid-io-file-pvt-p nil a1)
        (fw16-p-valid-io-file-pvt-p nil a3)
        (fw16-p-valid-io-file-pvt-p nil a5)
        (fw16-addr-le-p buffer-pointer data-pointer)
        (fw16-valid-rw-p write-start i4)
        (fw16-valid-rw-p write-start x)
        (fw16-separated-p a5 11 next-file 11)
        (fw16-separated-p a5 11 previous-file 11)
        (fw16-separated-p next-file 11 previous-file 11)
        (fw16-addr-lt-p
         data-pointer
         (fw16-shift buffer-pointer 16416))
        (fw16-valid-rw-p buffer-start 16416)
        (fw16-p-valid-file-p
         updated-integer-memory
         public-file)
        (fw16-separated-p a5 11 buffer-start 16416)
        (fw16-separated-p next-file 11 buffer-start 16416)
        (fw16-separated-p previous-file 11 buffer-start 16416)
        (fw16-p-valid-io-file-pvt-norec-p
         updated-integer-memory
         next-file)
        (fw16-p-valid-io-file-pvt-norec-p
         updated-integer-memory
         previous-file)
        (fw16-interval-exclusion-p i4 x a4))
       (fw16-p-valid-io-file-pvt-p
        updated-integer-memory
        a5))))))

(value-triple :itpeval-statement-checked)

:q
