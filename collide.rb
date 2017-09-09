#!/usr/bin/env ruby
require 'ffi'
require 'digest'
require 'optparse'

module LibColl
 extend FFI::Library

 ffi_lib 'coll-jpeg'
 attach_function :MD5CollideBlock0, [:pointer, :pointer, :string], :void 
 attach_function :MD5CollideBlock1, [:pointer, :pointer, :string], :void
 attach_function :MD5Transform, [:pointer, :pointer], :void

 def self.find_collision(iv, bad_chars)
   iv_pointer = to_iv_pointer(iv)
   output_pointer = FFI::MemoryPointer.new :uint, 16
  
   self.MD5CollideBlock0(iv_pointer, output_pointer, bad_chars)
   block0a = output_pointer.read_array_of_uint32 16
   self.MD5Transform(iv_pointer, output_pointer)
   self.MD5CollideBlock1(iv_pointer, output_pointer, bad_chars)
   block1a = output_pointer.read_array_of_uint32 16

   blocka = (block0a + block1a).pack("<L*")

   block0b = block0a
   block1b = block1a

   block0b[4] = (block0b[4] + (1<<31)) & 0xffffffff
   block0b[11] = (block0b[11] + (1<<15)) & 0xffffffff
   block0b[14] = (block0b[14] + (1<<31)) & 0xffffffff
   block1b[4] = (block1b[4] - (1<<31)) & 0xffffffff
   block1b[11] = (block1b[11] - (1<<15)) & 0xffffffff
   block1b[14] = (block1b[14] - (1<<31)) & 0xffffffff

   blockb = (block0b + block1b).pack("<L*")

   [blocka, blockb]
 end

 def self.md5_transform(iv, block)
   iv_pointer = to_iv_pointer(iv)
   block_pointer = FFI::MemoryPointer.new :uint, 16
   block_pointer.put_array_of_uint 0, block
   self.MD5Transform(iv_pointer, block_pointer)
 end

 def self.to_iv_pointer(iv)
   iv_pointer = FFI::MemoryPointer.new :uint, 4
   iv_pointer.put_array_of_uint 0, iv
   iv_pointer
 end

 def self.md5_transform_buffer(iv, buffer)
   if buffer.bytesize % 64 != 0
     raise "buffer wrong size #{buffer.bytesize}"
   end

   iv_pointer = to_iv_pointer(iv)
   block_pointer = FFI::MemoryPointer.new :uint, 16
   
   buffer.bytes.each_slice(64) do |block|
     block_pointer.put_array_of_uint8 0, block

     self.MD5Transform(iv_pointer, block_pointer)
   end 
   iv_pointer.read_array_of_uint 4
 end
end

def npad(p)
  "\x00" * p

end

def read_image(f)

  bytes = File.read(f, encoding: 'ascii-8bit')
  if bytes[0..1] != "\xff\xd8".b
    raise "not a jpeg"
  end
 
  bytes[2..-1]
end 
  
def read_images(image_names)
  image_names.map do |image|
    read_image(image)
  end
end

def calculate_iv(iv, prefix, buf)
  if prefix.nil?
    LibColl.md5_transform_buffer(iv, buf)
  else
    contents = prefix + buf
    LibColl.md5_transform_buffer(iv, contents)
 
  end

end

class Substitution < Struct.new(:position, :blocka, :blockb); end

MD5_BLOCK_SIZE = 64

iv = [0x67452301,0xefcdab89,0x98badcfe,0x10325476]
prefix_file = nil
pos = 0

OptionParser.new do |opts|
  opts.banner = "Usage: collide.rb [options] output_directory file1 file2 .."

  opts.on("--iv INT1,INT2,INT3,INT4", Array) do |iv_arg|
    if iv_values.length != 4
      puts "--iv requires 4 arguments"
      exit 1
    end
    iv = iv_values.map {|x| Integer(x)}
  end

  # calculate iv from file
  opts.on("--prefix FILE") do |prefix_file_arg|
    prefix_file = prefix_file_arg
  end

  opts.on("--position POS") do |pos_arg|
    pos = Integer(pos_arg)
  end


end.parse!

output_directory = ARGV.shift

image_names = ARGV
images = read_images(image_names)

if images.length < 2
  puts "need at least two images"
  exit 1
end

prefix = nil
if !prefix_file.nil?
  prefix = File.read(prefix_file, pos, 0, encoding: 'ascii-8bit')
end

buf = "".b
buf << "\xff\xd8".b

substitutions = []

(images.length - 1).times do |image_index|
  next_image = images[image_index]


  buf << "\xff\xfe".b

  align_bytes = (MD5_BLOCK_SIZE - (pos + 2 + buf.bytesize) % MD5_BLOCK_SIZE)

  # we could use a tree to reduce the collisions to log2(images) but the comment size is limited to 2^16
  # so with large numbers of images you need to jump over lots of images so you will hit this limit and then
  # be forced to put comments into the middle of other trees which makes things a lot more complicated :(

  # For two images:
  # [SOI][COMMENT_TAG][COMMENT_LENGTH][ALIGN_BYTES][CBLOCK1][CBLOCK2][COMMENT_A_PADDING][COMMENT_A_COMMENT_JUMP][COMMENT_B_PADDING][B_IMG][A_IMG]

  # For three images:
  # [SOI][COMMENT_TAG][COMMENT_LENGTH][ALIGN_BYTES][CBLOCK1][CBLOCK2][COMMENT_A_PADDING][COMMENT_A_COMMENT_JUMP][COMMENT_B_PADDING][B_IMG]
  #      [COMMENT_TAG][COMMENT_LENGTH][ALIGN_BYTES][CBLOCK1][CBLOCK2][COMMENT_A_PADDING][COMMENT_A_COMMENT_JUMP][COMMENT_B_PADDING][A_IMG][C_IMG]


  comment_offset = 56
  comment_size = 2 + align_bytes + comment_offset

  buf << [comment_size].pack("S>")
  buf << npad(align_bytes)

  new_iv = calculate_iv(iv, prefix, buf)

  blocka,blockb = LibColl.find_collision(new_iv, nil)


  if (blocka[comment_offset..comment_offset + 2] != "\xff\xfe\x00".b) || (blockb[comment_offset..comment_offset + 2] != "\xff\xfe\x00".b)
    raise StandardError, "missing comment block"
  end

  prefix_or_empty = prefix.nil? ? "" : prefix

  if Digest::MD5.digest(prefix_or_empty + buf + blocka) != Digest::MD5.digest(prefix_or_empty + buf + blockb)
    raise StandardError, "digest mismatch"
  end

  if blocka.getbyte(comment_offset + 3) > blockb.getbyte(comment_offset + 3)
    blocka, blockb = blockb, blocka
  end

  comment_a_size = blocka.getbyte(comment_offset + 3)
  comment_b_size = blockb.getbyte(comment_offset + 3)

  if comment_b_size - comment_a_size != 128
    raise StandardError, "wrong size difference: #{comment_b_size} #{comment_a_size}"
  end

  minimum_comment_length = (MD5_BLOCK_SIZE + MD5_BLOCK_SIZE - (comment_offset + 2))
  if comment_a_size < minimum_comment_length
    raise StandardError, "comment size not large enough: #{comment_a_size}"
  end

  substitutions << Substitution.new(buf.bytesize, blocka, blockb)

  buf << blocka

  comment_a_padding = (comment_a_size - minimum_comment_length)
  buf << npad(comment_a_padding)


  start_of_b_image = comment_b_size
  end_of_b_image = start_of_b_image + next_image.bytesize
  start_of_comment_a_jump = comment_a_size + 2
  comment_a_jump_size = end_of_b_image - start_of_comment_a_jump

  buf << "\xff\xfe".b
  buf << [comment_a_jump_size].pack("S>")

  comment_b_padding = comment_b_size - (start_of_comment_a_jump + 2)

  buf << npad(comment_b_padding)
  buf << next_image

  if image_index == images.length - 2
    last_image = images[images.length - 1]
    buf << last_image
  end
end

File.write(File.join(output_directory, File.basename(image_names[image_names.length - 1])), buf)

substitutions.each_with_index do |sub, i|
  output = File.join(output_directory, File.basename(image_names[i]))
  buf[sub.position..sub.position + sub.blockb.bytesize - 1] = sub.blockb
  File.write(output, buf)
  buf[sub.position..sub.position + sub.blocka.bytesize - 1] = sub.blocka

end
