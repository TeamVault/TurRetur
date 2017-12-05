//===-- llvm/Transforms/IPO/SDEncode.h --------*- C++ -*-------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_SDENCODE_H
#define LLVM_SDENCODE_H

#include "llvm/IR/DerivedTypes.h"
#include "llvm/Transforms/IPO/SafeDispatchLogStream.h"
#include <map>

namespace llvm {

/** Contains the three relevant encodings */
struct SDEncoding {
public:
  SDEncoding() = default;

  SDEncoding(uint64_t _Normal, uint64_t _Short, uint64_t _Precise) {
    Normal = _Normal;
    Short = _Short;
    Precise = _Precise;
  }

  uint64_t Normal;
  uint64_t Short;
  uint64_t Precise;

  static uint16_t encodeType(const Type* T, bool recurse = true) {
    uint16_t TypeEncoded;
    switch (T->getTypeID()) {
      case Type::TypeID::VoidTyID:
        TypeEncoded = 1;
        break;

      case Type::TypeID::IntegerTyID: {
        auto Bits = cast<IntegerType>(T)->getBitWidth();
        if (Bits <= 1) {
          TypeEncoded = 2;
        } else if (Bits <= 8) {
          TypeEncoded = 3;
        } else if (Bits <= 16) {
          TypeEncoded = 4;
        } else if (Bits <= 32) {
          TypeEncoded = 5;
        } else {
          TypeEncoded = 6;
        }
      }
        break;

      case Type::TypeID::HalfTyID:
        TypeEncoded = 7;
        break;
      case Type::TypeID::FloatTyID:
        TypeEncoded = 8;
        break;
      case Type::TypeID::DoubleTyID:
        TypeEncoded = 9;
        break;

      case Type::TypeID::X86_FP80TyID:
      case Type::TypeID::FP128TyID:
      case Type::TypeID::PPC_FP128TyID:
        TypeEncoded = 10;
        break;

      case Type::TypeID::PointerTyID:
        if (recurse) {
          TypeEncoded = uint16_t(16) + encodeType(dyn_cast<PointerType>(T)->getElementType(), false);
        } else {
          TypeEncoded = 11;
        }
        break;
      case Type::TypeID::StructTyID:
        TypeEncoded = 12;
        break;
      case Type::TypeID::ArrayTyID:
        TypeEncoded = 13;
        break;
      default:
        TypeEncoded = 14;
        break;
    }
    assert(TypeEncoded < 32);
    return TypeEncoded;
  }

  static uint64_t encodeFunction(const FunctionType *FuncTy, bool encodePointers, bool encodeReturnType) {
    uint64_t Encoding = 32;
    if (FuncTy->getNumParams() < 8) {
      if (encodeReturnType)
        Encoding = encodeType(FuncTy->getReturnType(), encodePointers);

      for (auto *Param : FuncTy->params()) {
        Encoding = encodeType(Param) + Encoding * 32;
      }
    }
    return Encoding;
  }

  static SDEncoding encode(const FunctionType* Type) {
    auto Encoding = encodeFunction(Type, true, false);
    auto EncodingShort = encodeFunction(Type, false, false);
    auto EncodingPrecise = encodeFunction(Type, true, true);
    return {Encoding, EncodingShort, EncodingPrecise};
  }
};

class SDEncoder {
public:
  explicit SDEncoder(uint32_t StartTypeID) : NextTypeID(StartTypeID) {}

  uint32_t getTypeID(FunctionType *FuncTy) {
    auto Encoding = SDEncoding::encodeFunction(FuncTy, true, true);
    if (EncodingToTypeID.find(Encoding) == EncodingToTypeID.end()) {
      sdLog::log() << "New FunctionTypeID " << NextTypeID << ": " << *FuncTy << "\n";
      EncodingToTypeID[Encoding] = NextTypeID;
      --NextTypeID;
    }
    return EncodingToTypeID[Encoding];
  }

private:
  uint32_t NextTypeID;
  std::map<uint64_t, uint32_t> EncodingToTypeID {};
};

} // End llvm namespace

#endif //LLVM_SDENCODE_H
