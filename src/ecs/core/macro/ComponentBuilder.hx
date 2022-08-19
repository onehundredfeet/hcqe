package ecs.core.macro;

import ecs.utils.Const;
#if macro
import ecs.core.macro.MacroTools.*;
import haxe.macro.Type;
import haxe.macro.Printer;
import haxe.macro.Expr;

using ecs.core.macro.MacroTools;
using Lambda;
using tink.MacroApi;
using haxe.macro.ComplexTypeTools;
using haxe.macro.TypeTools;
using haxe.macro.Context;
using haxe.ds.ArraySort;

typedef MetaMap = haxe.ds.Map<String, Array<Array<Expr>>>;

@:enum abstract StorageType(Int) from Int to Int {
	var FAST = 0; // An array the length of all entities, with non-null meaning membership
	var COMPACT = 1; // A map from entity to members
	var SINGLETON = 2; // A single reference with a known entity owner
	var TAG = 3; // An bitfield the length of all entities, with ON | OFF meaning membership

	//  var GLOBAL = 4;     // Exists on every entity
	//  var TRANSIENT = 5;  // Automatically removed every tick
	//  var NONE = 6; 		// This class is not allowed to be used as a component
	public static function getStorageType(mm:MetaMap) {
		var storageType = StorageType.FAST;

		var stma = mm.get(":storage");

		if (stma != null) {
			var stm = stma[0];
			return switch (stm[0].expr) {
				case EConst(CIdent(s)), EConst(CString(s)):
					switch (s.toUpperCase()) {
						case "FAST": FAST;
						case "COMPACT": COMPACT;
						case "SINGLETON": SINGLETON;
						case "TAG": TAG;
						default:
							Context.warning('Unknown storage type ${s}', Context.currentPos());
							FAST;
					}
				default: FAST;
			}
		}
		return FAST;
	}
}

var _printer = new Printer();
@:persistent var createdModule = false;
final modulePrefix = "__ecs__storage";
@:persistent var tagMap = new Map<String, Int>();
@:persistent var tagCount = 0;

function getModulePath():String {
	if (!createdModule) {
		Context.defineModule(modulePrefix, []);
	}
	return modulePrefix;
}

class StorageInfo {
	public static final STORAGE_NAMESPACE = "ecs.storage";

	static function getPooled(mm:MetaMap) {
		var bb = mm.get(":build");

		if (bb != null) {
			for (b in bb) {
				switch (b[0].expr) {
					case ECall({ expr: EField(fe, _) }, _)
						if (fe.toString() == "ecs.core.macro.PoolBuilder"):
						return true;
					default:
				}
			}
		}
		return false;
	}

	public function new(ct:ComplexType, i:Int, pos) {
		// trace ('Generating storage for ${ct.toString()}');
		givenCT = ct;
		followedCT = ct.followComplexType(pos);
		followedT = followedCT.toTypeOrNull(Context.currentPos());
		if (followedT == null) {
			Context.error('Could not find type for ${ct}', Context.currentPos());
		}
		followedClass = null;
		try {
			followedClass = followedT.getClass();
		} catch (e) {
			switch (followedT) {
				case TAbstract(at, params):
					var x = at.get().impl;
					if (x != null) {
						followedClass = x.get();
					} else {
						Context.warning('abstract not implemented ${followedCT.toString()}', Context.currentPos());
					}
				default:
					Context.warning('Couldn\'t find class ${followedCT.toString()}', Context.currentPos());
			}
		}

		followedMeta = followedT.getMeta().flatMap((x) -> x.get()).toMap();

		var rt = followedT.followWithAbstracts();

		emptyExpr = switch (rt) {
			case TInst(_, _): macro null;
			case TAbstract(_.get() => { name: "Int" }, _):
				macro 0;
			default: macro null;
		}
		//		trace('Underlaying type is ${rt} with empty ${_printer.printExpr(emptyExpr)}');

		//		followedMeta.exists(":empty") ? followedMeta.get(":empty")[0][0] : macro null;

		fullName = followedCT.followComplexType(pos).typeFullName(pos);
		storageType = StorageType.getStorageType(followedMeta);
		//		isPooled = getPooled(followedMeta);
		isPooled = false;
		var tp = (switch (storageType) {
			case FAST: tpath([], "Array", [TPType(followedCT)]);
			case COMPACT: tpath(["haxe", "ds"], "IntMap", [TPType(followedCT)]);
			case SINGLETON: followedCT.toString().asTypePath();
			case TAG: null;
				// case TAG: tpath([], "Array", [TPType(followedCT)]); // TODO [RC] - Optimize tag path
		});

		componentIndex = i;

		if (tp != null) {
			storageCT = TPath(tp);

			containerTypeName = 'StorageOf' + fullName;
			containerFullName = STORAGE_NAMESPACE + "." + containerTypeName;

			containerFullNameExpr = containerFullName.asTypeIdent(Context.currentPos());

			//		Context.registerModuleDependency()
			containerCT = containerFullName.asComplexType();
			containerType = containerCT.toTypeOrNull(Context.currentPos());

			if (containerType == null) {
				var existsExpr = getExistsExpr(macro id);
				var removeExpr = getRemoveExpr(macro id);

				var def = (storageType == SINGLETON) ? macro class $containerTypeName {
					public static var storage:$storageCT;
					public static var owner:Int = 0;
				} : macro class $containerTypeName {
					public static var storage:$storageCT = new $tp();

					public function exists(id:Int)
						return $existsExpr;
					};

				//			trace(_printer.printTypeDefinition(def));
				def.defineTypeSafe(STORAGE_NAMESPACE, Const.ROOT_MODULE);
			}

			if (containerType == null) {
				containerType = containerCT.toTypeOrNull(Context.currentPos());
			}
		} else {
			containerCT = null;
			containerType = null;
			containerTypeName = null;
			containerFullName = null;
			containerFullNameExpr = null;
		}
		
	}

	public inline function requiresStorage() : Bool {
		return (storageType != TAG);
	}
	function tagExpr() : Expr {
		if (!tagMap.exists(fullName)) {
			tagMap.set(fullName, tagCount++);
		}

		return EConst(CInt(Std.string(tagMap.get(fullName)))).at();
	}
	public function getGetExpr(entityExpr:Expr, cachedVarName:String = null):Expr {
		var container = cachedVarName != null ? macro $i{cachedVarName} : macro $containerFullNameExpr.storage;
		return switch (storageType) {
			case FAST: macro $container[$entityExpr];
			case COMPACT: macro $container.get($entityExpr);
			case SINGLETON: macro $container;
			case TAG: var te = tagExpr();
			  macro @:privateAccess ecs.Workflow.getTag($entityExpr, $te) ? 1 : 0;
		};
	}

	public function getExistsExpr(entityVar:Expr):Expr {
		return switch (storageType) {
			case FAST: macro $containerFullNameExpr.storage[$entityVar] != $emptyExpr;
			case COMPACT: macro $containerFullNameExpr.storage.exists($entityVar);
			case SINGLETON: macro $containerFullNameExpr.owner == $entityVar;
			case TAG: 
				var te = tagExpr();	
				macro  @:privateAccess ecs.Workflow.getTag($entityVar, $te);
		};
	}

	public function getCacheExpr(cacheVarName:String):Expr {
		return cacheVarName.define(macro $containerFullNameExpr.storage);
	}

	public function getAddExpr(entityVarExpr:Expr, componentExpr:Expr):Expr {
		return switch (storageType) {
			case FAST: macro $containerFullNameExpr.storage[$entityVarExpr] = $componentExpr;
			case COMPACT: macro $containerFullNameExpr.storage.set($entityVarExpr, $componentExpr);
			case SINGLETON: macro {
					if ($containerFullNameExpr.owner != 0)
						throw 'Singleton already has an owner';
					$containerFullNameExpr.storage = $componentExpr;
					$containerFullNameExpr.owner = $entityVarExpr;
				};
			case TAG:var te = tagExpr();	
			macro @:privateAccess  ecs.Workflow.setTag($entityVarExpr, $te);
		};
	}

	public function getRemoveExpr(entityVarExpr:Expr):Expr {
		if (storageType == TAG) {
			var te = tagExpr();	
			return  macro @:privateAccess ecs.Workflow.clearTag($te, $te);	
		}

		var accessExpr = switch (storageType) {
			case FAST: macro @:privateAccess $containerFullNameExpr.storage[$entityVarExpr];
			case COMPACT: macro @:privateAccess $containerFullNameExpr.storage.get($entityVarExpr);
			case SINGLETON: macro($containerFullNameExpr.owner == $entityVarExpr ? $containerFullNameExpr.storage : null);
			case TAG: var te = tagExpr();	
			@:privateAccess  macro ecs.Workflow.getTag($te, $te);
		};

		var hasExpr = getExistsExpr(entityVarExpr);
		var retireExprs = new Array<Expr>();
		var autoRetire = isPooled && !followedMeta.exists(":no_auto_retire");
		if (autoRetire) {
			retireExprs.push(macro $accessExpr.retire());
		}

		if (followedClass != null) {
			var cfs_statics = followedClass.statics.get().map((x) -> {cf: x, stat: true});
			var cfs_non_statics = followedClass.fields.get().map((x) -> {cf: x, stat: false});

			var cfs = cfs_statics.concat(cfs_non_statics);

			for (cfx in cfs) {
				switch (cfx.cf) {
					case { name: name, kind: FMethod(_), meta: meta,
						expr: _().expr => TFunction(tfunc) }
						if (meta.has(":ecs_remove")):
						var needsEntity = false;
						for (a in tfunc.args) {
							if (a.v.t.toComplexType().toString() == (macro:ecs.Entity).toString()) {
								needsEntity = true;
								break;
							}
						}
						if (needsEntity) {
							retireExprs.push(macro @:privateAccess $accessExpr.$fname($entityVarExpr));
						} else {
							// trace('removing without entity ${cf.name} | ${tfunc.args.length} | ${ cfx.stat} in ${followedClass.name}');
							retireExprs.push(macro @:privateAccess $accessExpr.$fname());
						}
					default:
				}
			}
		}

		return switch (storageType) {
			case FAST: macro if ($hasExpr) {
					$b{retireExprs} @:privateAccess $containerFullNameExpr.storage[$entityVarExpr] = $emptyExpr;
				}
			case COMPACT: macro if ($hasExpr) {
					$b{retireExprs} @:privateAccess $containerFullNameExpr.storage.remove($entityVarExpr);
				}
			case SINGLETON: macro if ($hasExpr) {
					$b{retireExprs} $containerFullNameExpr.storage = $emptyExpr;
					$containerFullNameExpr.owner = 0;
				}
			case TAG:
				var te = tagExpr();	
				@:privateAccess  macro ecs.Workflow.clearTag($te, $te);	
		};
	}

	public final givenCT:ComplexType;
	public final followedT:haxe.macro.Type;
	public final followedCT:ComplexType;
	public final followedMeta:MetaMap;
	public final followedClass:ClassType;
	public final storageType:StorageType;
	public final storageCT:ComplexType;
	public final componentIndex:Int;
	public final fullName:String;
	public final containerCT:ComplexType;
	public final containerType:haxe.macro.Type;
	public final containerTypeName:String;
	public final containerFullName:String;
	public final containerFullNameExpr:Expr;
	public final emptyExpr:Expr;
	public final isPooled:Bool;
}

class ComponentBuilder {
	static var componentIndex = -1;
	static var componentContainerTypeCache = new Map<String, StorageInfo>();

	public static function containerNames() {
		return componentContainerTypeCache.keys();
	}

	public static function getComponentContainerInfoByName(s:String) {
		return componentContainerTypeCache[s];
	}

	public static function getComponentContainerInfo(componentComplexType:ComplexType, pos):StorageInfo {
		var name = componentComplexType.followName(pos);

		var info = componentContainerTypeCache.get(name);
		if (info != null) {
			return info;
		}

		info = new StorageInfo(componentComplexType, ++componentIndex, pos);
		componentContainerTypeCache[name] = info;

		return info;
	}

	public static function getLookup(ct:ComplexType, entityVarName:Expr, pos):Expr {
		return getComponentContainerInfo(ct, pos).getGetExpr(entityVarName);
	}

	public static function getComponentId(componentComplexType:ComplexType, pos):Int {
		return getComponentContainerInfo(componentComplexType, pos).componentIndex;
	}
}
#end
