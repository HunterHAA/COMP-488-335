---- ---- MODULE MC ----
EXTENDS BoundedBuffer, TLC

const_producers == 10
const_consumers == 5
const_BufferSize == 4

====