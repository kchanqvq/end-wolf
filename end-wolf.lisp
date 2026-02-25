(uiop:define-package #:end-wolf
  (:use #:cl #:iterate #:alexandria))

(in-package #:end-wolf)

;;; Encoder: made fast

(declaim (type (simple-array (unsigned-byte 32) (26 23)) *binomial-table*)
         (inline encode-mask next-mask))

(deftype state () '(unsigned-byte 35))
(deftype board () '(unsigned-byte 25))
(deftype bitpos () '(unsigned-byte 5))

(sb-ext:defglobal *binomial-table*
    (let ((table (make-array '(26 23) :initial-element 0 :element-type '(unsigned-byte 32))))
      (loop for n from 0 below 26 do
        (setf (aref table n 0) 1)
        (loop for k from 1 to (min n 22) do
          (setf (aref table n k)
                (+ (aref table (1- n) (1- k))
                   (aref table (1- n) k)))))
      table))

(defun encode-mask (sheep-mask wolf-mask n)
  (declare (optimize speed)
           (board sheep-mask wolf-mask)
           (bitpos n))
  (let ((result 0) (all-mask (logior sheep-mask wolf-mask)))
    (declare (state result) (board all-mask))
    (macrolet ((gen-binom (k i)
                 (cond
                   ((<= i 10)
                    `(floor (the (unsigned-byte 64)
                                 (* ,@(iter (for d from 0 below i)
                                        (collect `(- ,k ,d)))))
                            ,(factorial i)))
                   (t `(aref *binomial-table* ,k ,i))))
               (process-wolf (i)
                    `(let* ((low-bit (logand wolf-mask (- wolf-mask)))
                            (k (logcount (logand (1- low-bit) all-mask))))
                       (incf result (gen-binom k ,i))
                       ,(unless (= i 3)
                          `(setq wolf-mask (logxor wolf-mask low-bit)))))
               (process-all (i)
                 `(progn
                    (unless (<= ,i n)
                      (return-from encode-mask result))
                    (let* ((low-bit (logand all-mask (- all-mask)))
                           (k (1- (integer-length low-bit))))
                      (incf result (gen-binom k ,i))
                     (setq all-mask (logxor all-mask low-bit)))))
               (gen-all ()
                 `(progn ,@(iter (for i from 1 to 18)
                             (collect `(process-all ,i))))))
      (process-wolf 1)
      (process-wolf 2)
      (process-wolf 3)
      (setq result (* result (aref *binomial-table* 25 n)))
      (gen-all)
      result)))

(defun decode-set (cns-code n)
  (let (result)
    (iter (with last = 25)
      (for m from n downto 1)
      (iter (for k from (1- last) downto 0)
        (for c = (aref *binomial-table* k m))
        (when (<= c cns-code)
          (decf cns-code c)
          (push (setf last k) result)
          (return))))
    result))

;;; Decoder: not in hot loop, no need to be fast

;; non-inclusive
(defun max-state (n-pieces)
  (* (aref *binomial-table* 25 n-pieces) (aref *binomial-table* n-pieces 3)))

(defun decode-mask (code n)
  (multiple-value-bind (wolf-code all-code)
      (floor code (aref *binomial-table* 25 n))
    (let ((wolf-pos (decode-set wolf-code 3))
          (all-pos (decode-set all-code n))
          (sheep-mask 0)
          (wolf-mask 0))
      (iter (for i from 0 below 25)
        (with j = 0)
        (when (eql i (car all-pos))
          (pop all-pos)
          (if (eql j (car wolf-pos))
              (progn
                (pop wolf-pos)
                (setf (ldb (byte 1 i) wolf-mask) 1))
              (setf (ldb (byte 1 i) sheep-mask) 1))
          (incf j)))
      (values sheep-mask wolf-mask))))

;;; Convenience

(defun list-mask (sheep-mask wolf-mask)
  (iter (with i = 0)
    (for row from 0 below 5)
    (collecting
     (iter (for col from 0 below 5)
       (cond ((plusp (ldb (byte 1 i) wolf-mask))
              (collect 'w))
             ((plusp (ldb (byte 1 i) sheep-mask))
              (collect 's))
             (t
              (collect '-)))
       (incf i)))))

(defun print-mask (sheep-mask wolf-mask)
  (format t "(~{(~{~a~^ ~})~^~% ~})~%" (list-mask sheep-mask wolf-mask)))

(defun print-encoded (code n)
  (multiple-value-call #'print-mask (decode-mask code n)))

(defun list-encoded (code n)
  (multiple-value-call #'list-mask (decode-mask code n)))

(defun parse-mask (list)
  (let ((sheep-mask 0)
        (wolf-mask 0)
        (i 0)
        (count 0))
    (dolist (row list)
      (dolist (piece row)
        (ecase piece
          (w (setf (ldb (byte 1 i) wolf-mask) 1)
           (incf count))
          (s (setf (ldb (byte 1 i) sheep-mask) 1)
           (incf count))
          (-))
        (incf i)))
    (values sheep-mask wolf-mask count)))

(defun parse-encoded (list)
  (multiple-value-call #'encode-mask (parse-mask list)))

(defun random-board-list ()
  (iter (for wc = 0)
    (for sc = 0)
    (for board-list =
         (iter
           (for i below 5)
           (collecting
             (iter (for j below 5)
               (collecting
                 (case (random 5)
                   ((0 1) '-)
                   ((2 3) (if (< sc 15)
                              (prog1 's (incf sc))
                              '-))
                   (4 (if (< wc 3)
                          (prog1 'w (incf wc))
                          '-))))))))
    (when (and (= 3 wc) (<= 4 sc 14))
      (return (values board-list (+ wc sc))))))

(defun fuzz-encode-decode (seed)
  (let ((*random-state* (sb-ext:seed-random-state seed)))
    (iter (repeat 100000)
      (for (values board-list n) = (random-board-list))
      (for encoded = (parse-encoded board-list))
      (unless (equal board-list (list-encoded encoded n))
        (error "encode/decode does not round trip~%~a" board-list)))))

;;; Advance mask for state+1

(defun next-mask (sheep-mask wolf-mask n)
  (declare (optimize speed)
           (board wolf-mask sheep-mask)
           (bitpos n))
  (let* ((all-mask (logior wolf-mask sheep-mask))
         (movable (logandc2 all-mask (ash all-mask -1)))
         (lowest-movable (logand movable (- movable)))
         (shift (sb-kernel:count-trailing-zeros all-mask)))
    (if (< lowest-movable #.(ash 1 24))
        (let ((clear-mask (1- lowest-movable)))
          (values (logxor (+ (logandc2 sheep-mask clear-mask)
                             (logand sheep-mask lowest-movable))
                          (ash (logand sheep-mask clear-mask) (- shift)))
                  (logxor (+ (logandc2 wolf-mask clear-mask)
                             (logand wolf-mask lowest-movable))
                          (ash (logand wolf-mask clear-mask) (- shift)))))
        (let* ((wolf-mask (ash wolf-mask (- shift)))
               (movable (logandc2 wolf-mask (ash wolf-mask -1)))
               (lowest-movable (logand movable (- movable)))
               (shift (sb-kernel:count-trailing-zeros wolf-mask))
               (clear-mask (1- lowest-movable))
               (new-wolf (logxor (+ (logandc2 wolf-mask clear-mask)
                                    (logand wolf-mask lowest-movable))
                                 (ash (logand wolf-mask clear-mask) (- shift)))))
          (values (logxor (1- (ash 1 n)) new-wolf) new-wolf)))))

(declaim (inline sheep-forward wolf-forward
                 sheep-backward wolf-move-backward))

(defun sheep-forward (sm wm cont)
  (declare (optimize speed)
           (board wm sm)
           (function cont))
  (let ((em (lognot (logior wm sm))))
    (let ((right (logand sm (ash em -1) #b0111101111011110111101111)))
      (declare (board right))
      (loop while (plusp right) do
        (let ((low-bit (logand right (- right))))
          (setf right (logxor right low-bit))
          (funcall cont (+ sm low-bit) wm))))
    (let ((left-to (logand (ash sm -1) em #b0111101111011110111101111)))
      (declare (board left-to))
      (loop while (plusp left-to) do
        (let ((low-bit (logand left-to (- left-to))))
          (setf left-to (logxor left-to low-bit))
          (funcall cont (- sm low-bit) wm))))
    (let ((down (logand sm (ash em -5) #b0000011111111111111111111)))
      (declare (board down))
      (loop while (plusp down) do
        (let ((low-bit (logand down (- down))))
          (setf down (logxor down low-bit))
          (funcall cont (+ sm (* low-bit #b11111)) wm))))
    (let ((up-to (logand (ldb (byte 20 5) sm) em)))
      (declare (board up-to))
      (loop while (plusp up-to) do
        (let ((low-bit (logand up-to (- up-to))))
          (setf up-to (logxor up-to low-bit))
          (funcall cont (- sm (* low-bit #b11111)) wm))))))

(defun sheep-backward (sm wm cont)
  (sheep-forward sm wm cont))

(defun wolf-move-backward (sm wm cont)
  (sheep-forward wm sm (lambda (wm sm) (funcall cont sm wm))))

(defun wolf-forward (sm wm move-cont cap-cont)
  (declare (optimize speed)
           (board wm sm)
           (function move-cont cap-cont))
  (let ((em (lognot (logior wm sm))))
    (let* ((right (logand wm (ash em -1) #b0111101111011110111101111))
           (cap (logand right (ash sm -2) #b0011100111001110011100111)))
      (declare (board right cap))
      (loop while (plusp right) do
        (let ((low-bit (logand right (- right))))
          (setf right (logxor right low-bit))
          (funcall move-cont sm (+ wm low-bit))))
      (loop while (plusp cap) do
        (let ((low-bit (logand cap (- cap))))
          (setf cap (logxor cap low-bit))
          (funcall cap-cont (- sm (* low-bit #b100)) (+ wm (* low-bit #b11))))))
    (let* ((left-to (logand (ash wm -1) em #b0111101111011110111101111))
           (cap-to (logand (ash left-to -1) sm #b0011100111001110011100111)))
      (declare (board left-to cap-to))
      (loop while (plusp left-to) do
        (let ((low-bit (logand left-to (- left-to))))
          (setf left-to (logxor left-to low-bit))
          (funcall move-cont sm (- wm low-bit))))
      (loop while (plusp cap-to) do
        (let ((low-bit (logand cap-to (- cap-to))))
          (setf cap-to (logxor cap-to low-bit))
          (funcall cap-cont (- sm low-bit) (- wm (* low-bit #b11))))))
    (let* ((down (logand wm (ash em -5) #b0000011111111111111111111))
           (cap (logand down (ash sm -10) #b0000000000111111111111111)))
      (declare (board down cap))
      (loop while (plusp down) do
        (let ((low-bit (logand down (- down))))
          (setf down (logxor down low-bit))
          (funcall move-cont sm (+ wm (* low-bit #b11111)))))
      (loop while (plusp cap) do
        (let ((low-bit (logand cap (- cap))))
          (setf cap (logxor cap low-bit))
          (funcall cap-cont (- sm (* low-bit #b10000000000))
                   (+ wm (* low-bit #b1111111111))))))
    (let* ((up-to (logand (ldb (byte 20 5) wm) em))
           (cap-to (logand (ldb (byte 20 5) up-to) sm)))
      (declare (board up-to cap-to))
      (loop while (plusp up-to) do
        (let ((low-bit (logand up-to (- up-to))))
          (setf up-to (logxor up-to low-bit))
          (funcall move-cont sm (- wm (* low-bit #b11111)))))
      (loop while (plusp cap-to) do
        (let ((low-bit (logand cap-to (- cap-to))))
          (setf cap-to (logxor cap-to low-bit))
          (funcall cap-cont (- sm low-bit) (- wm (* low-bit #b1111111111))))))))
